# ML-KEM matrix-arithmetic core: impl ↔ spec equivalence

This tree contains the Lean 4 proof that the Rust implementation of
ML-KEM's polynomial **matrix-arithmetic core** in `libcrux-iot/ml-kem/src/`
computes the same functions as the hacspec-style specification in
`specs/ml-kem/src/`. Both sides are auto-extracted via the
[hax → aeneas → aeneas-lean](https://github.com/AeneasVerif/aeneas)
pipeline; this directory then proves their functional-correctness (FC)
equivalence.

The four top-level results are the arithmetic heart of ML-KEM IND-CPA
key-generation, encryption, and decryption: the matrix–vector and
vector–vector products in the NTT domain, their inverse-NTT, and the
error/message combination steps. The surrounding glue (XOF expansion,
rejection sampling, (de)serialization, compression) is **not** proven
here — see [Assumptions](#assumptions-trust-boundary) for the precise
trust boundary.

## Matrix-level theorems

All four are `@[spec]` Triples of the form
`⦃ True ⦄ <impl> ⦃ ⇓ p => ⌜ <hacspec> (lift args…) = .ok (lift p…) ⌝ ⦄`
— i.e. equality-form total-correctness postconditions coupling the
Aeneas-extracted impl to the hacspec spec through a `lift` bridge into
the spec's `ZMod 3329`-backed field representation.

### L7.1 — key generation: `Â · ŝ + ê`

[`BitMlKem/FCTargets.lean`](BitMlKem/FCTargets.lean) — `compute_As_plus_e_fc`:

```lean
⦃ ⌜ True ⌝ ⦄
matrix.compute_As_plus_e K portable_ops_inst matrix_A s_as_ntt error_as_ntt …
⦃ ⇓ p => ⌜ hacspec_ml_kem.matrix.compute_As_plus_e
              (lift_matrix_from_slice matrix_A K)
              (lift_vec s_as_ntt) (lift_vec error_as_ntt)
            = .ok (lift_vec p.1) ⌝ ⦄
```

The impl's `K×K` matrix · `K`-vector product plus error, lifted, equals
the hacspec `compute_As_plus_e`. The matrix is read from a **stored**
`K×K` array (`lift_matrix_from_slice`), so this theorem is fully
axiom-clean.

### L7.2 — encryption: `Âᵀ · r̂ + ê₁`

[`BitMlKem/L7/FC/ComputeVectorU.lean`](BitMlKem/L7/FC/ComputeVectorU.lean) — `compute_vector_u_fc`:

```lean
⦃ ⌜ True ⌝ ⦄
matrix.compute_vector_u K portable_ops_inst … seed r_as_ntt error_1 …
⦃ ⇓ p => ⌜ hacspec_ml_kem.matrix.compute_vector_u
              (lift_matrix_from_seed seed K)
              (lift_vec_slice r_as_ntt K) (lift_vec_slice error_1 K)
            = .ok (lift_vec_slice p.2.1 K) ⌝ ⦄
```

The transposed matrix · vector product plus `e₁`. Here the matrix is
**sampled on the fly** from `seed` (`lift_matrix_from_seed`), so this
theorem is conditional on the matrix-sampling leaf axiom **A1** (see
[Assumptions](#assumptions-trust-boundary)).

### L7.3 — encryption: `t̂ · r̂ + e₂ + Decompress(message)`

[`BitMlKem/L7/FC/ComputeRingElementV.lean`](BitMlKem/L7/FC/ComputeRingElementV.lean) — `compute_ring_element_v_fc`:

```lean
⦃ ⌜ True ⌝ ⦄
matrix.compute_ring_element_v K portable_ops_inst
  public_key t_as_ntt_entry r_as_ntt error_2 message result scratch cache accumulator
⦃ ⇓ p => ⌜ hacspec_ml_kem.matrix.compute_ring_element_v
              (lift_t_as_ntt_from_public_key public_key K)
              (lift_vec_slice r_as_ntt K)
              (lift_poly error_2) (lift_poly message)
            = .ok (lift_poly p.2.1) ⌝ ⦄
```

The vector·vector inner product `t̂ · r̂`, inverse-NTT'd, plus `e₂` and
the (decompressed) message. The first vector `t̂` is **deserialized**
from the public key (`lift_t_as_ntt_from_public_key`), so this theorem
is conditional on the deserialization leaf axiom **A2** (see
[Assumptions](#assumptions-trust-boundary)).

### L7.4 — decryption: `NTT⁻¹(v̂ − ŝ · û)`

[`BitMlKem/L7/FC/ComputeMessage.lean`](BitMlKem/L7/FC/ComputeMessage.lean) — `compute_message_fc`:

```lean
⦃ ⌜ True ⌝ ⦄
matrix.compute_message K portable_ops_inst v secret_as_ntt u_as_ntt …
⦃ ⇓ p => ⌜ hacspec_ml_kem.matrix.compute_message
              (lift_poly v) (lift_vec secret_as_ntt) (lift_vec u_as_ntt)
            = .ok (lift_poly p.1) ⌝ ⦄
```

`v − secret · u`, then inverse-NTT. All inputs are passed-in polynomials
(`lift_poly` / `lift_vec`), so this theorem is fully axiom-clean.

## Polynomial-level theorems

The four matrix-level theorems above are assembled from a stack of
**polynomial-level** FC theorems — each over a single ring element
(`PolynomialRingElement` = 256 coefficients) — stated and proven in
[`BitMlKem/FCTargets.lean`](BitMlKem/FCTargets.lean). Unlike L7.2/L7.3,
**none** of these depend on the sampling / deserialization leaf axioms or
the spec stubs: every one reports only `{propext, Classical.choice,
Quot.sound}` (verified). They are the unconditionally-proven core of the
development.

Each has the same equality shape as the matrix theorems —
`lift_poly p = Spec.<op>_pure (lift_poly …)` (or the hacspec-`Result`
form `… = .ok (lift_poly p)`).

### Number-theoretic transform — forward (`ntt_pure`)

```lean
-- ntt_binomially_sampled_ring_element_fc
⦃ ⌜ True ⌝ ⦄ polynomial.…ntt_binomially_sampled_ring_element … re
⦃ ⇓ p => ⌜ lift_poly p.1 = Spec.ntt_pure (lift_poly re) ⌝ ⦄
```

The impl's in-place 7-layer forward NTT equals the spec's `Spec.ntt_pure`.
The ciphertext-`u` variant `ntt_vector_u_fc` (`= Spec.ntt_pure_vec_u`)
covers the encryption path. Both are composed from the per-layer butterfly
drivers `ntt_at_layer_{1,2,3,7}_portable_fc` and
`ntt_at_layer_4_plus_portable_fc` — each with a bound-carrying `_strong`
variant that threads the per-lane `|coeff|` growth across layers.

### Number-theoretic transform — inverse (`invert_ntt_montgomery_pure`)

```lean
-- invert_ntt_montgomery_fc
⦃ ⌜ True ⌝ ⦄ … invert_ntt_montgomery K … re scratch
⦃ ⇓ p => ⌜ lift_poly p.1 = Spec.invert_ntt_montgomery_pure (lift_poly re)
            ∧ (∀ i j < 16, per-lane |coeff| bound) ⌝ ⦄
```

The inverse NTT (with the trailing `1/128` Montgomery scaling), built from
`invert_ntt_at_layer_{1,2,3}_portable_fc`,
`invert_ntt_at_layer_4_plus_portable_fc`, and the per-vector reduce step
`inv_ntt_layer_int_vec_step_reduce_fc`. The cross-domain `R`-factor of the
inverse is carried by the `scaleZ`-bridges (`invert_ntt_montgomery_pure_scaleZ`,
`ntt_inverse_eq_scaleZ_invert_pure`) used in the L7 chains.

### Pointwise NTT multiplication

```lean
-- multiply_ntts_eq_pure_array
ntt.multiply_ntts p1 p2
  = .ok ⟨(List.range 256).map (multiply_ntts_lane_pure p1 p2), …⟩
```

The base-case pointwise product of two NTT-domain ring elements, lane by
lane. The accumulating form `accumulating_ntt_multiply_poly_fc` adds the
product `self · rhs` into an `i32[256]` accumulator in the Montgomery
domain (characterized by `accumulating_ntt_multiply_poly_post` plus a
`≤ 2³⁰` growth bound); the cache variants
`accumulating_ntt_multiply_{fill,use}_cache_poly_fc` precompute / reuse the
per-lane twiddle cache. This kernel is the inner loop of all four
matrix-level products (the `scaleZ 2285` acc-bridges in
[`L7/Impl/`](BitMlKem/L7/Impl/) sit directly on top of it).

### Reduction, error, and message combination (L6)

The poly-level arithmetic that finishes each ML-KEM step. Every one couples
the impl op to its pure spec mirror `Spec.<op>_pure`:

| Theorem | hacspec op | what it does |
|---------|-----------|--------------|
| `poly_barrett_reduce_fc`          | `poly_barrett_reduce`               | Barrett-reduce all 256 lanes to canonical residues |
| `poly_reducing_from_i32_array_fc` | `poly_reducing_from_i32_array_pure` | Montgomery-reduce an `i32[256]` accumulator into a ring element |
| `subtract_reduce_fc`              | `subtract_reduce_pure`              | subtract two ring elements, then Barrett-reduce (decryption tail, L7.4) |
| `add_error_reduce_fc`             | `add_error_reduce_pure`             | add an error polynomial (impl's `1441`-Montgomery multiply), Barrett-reduce |
| `add_standard_error_reduce_fc`    | `add_standard_error_reduce_pure`    | add a standard error polynomial (`R`-Montgomery multiply), Barrett-reduce (keygen tail) |
| `add_message_error_reduce_fc`     | `add_message_error_reduce_pure`     | add error + message to the (`1441`-multiplied) result, Barrett-reduce (L7.3 tail) |

`poly_reducing_from_i32_array_fc` lands in the Montgomery domain
(`lift_poly_mont`); a `mont_strip` bridge in
[`L7/Common.lean`](BitMlKem/L7/Common.lean) converts it to the canonical
`lift_poly` the matrix-level chains consume.

### Field- and vector-element primitives (L0–L2)

Beneath the polynomial layer, each leaf is proven against its `ZMod 3329`
spec and chained upward:

- **L0** — per-coefficient field arithmetic: `add_fc`, `sub_fc`,
  `barrett_reduce_fc`, `montgomery_reduce_element_fc`,
  `montgomery_multiply_fe_by_fer_fc`, `montgomery_multiply_by_constant_fc`,
  `cond_subtract_3329_fc`, `get_n_least_significant_bits_fc`, …
- **L1** — the `PortableVector` 16-lane SIMD-shaped ops (`negate_fc`,
  `multiply_by_constant_fc`, `bitwise_and_with_constant_fc`,
  `shift_right_fc`, `reducing_from_i32_array_fc`, …).
- **L2** — single NTT butterfly steps within one layer: `ntt_step_fc`,
  `ntt_layer_{1,2,3}_step_fc`, `inv_ntt_step_fc`,
  `inv_ntt_layer_{1,2,3}_step_fc`.

These are the leaves the polynomial-level theorems compose.

## Assumptions (trust boundary)

The four matrix-arithmetic theorems above are **complete proofs** modulo
the assumptions below. Read this section as the precise statement of what
is *trusted* rather than *proven*.

### Standard Lean axioms

Every theorem depends on Lean's three classical axioms: `propext`,
`Classical.choice`, `Quot.sound`. There is **no** `native_decide` in the
proven path (no `Lean.ofReduceBool` / `Lean.trustCompiler`).

### Per-theorem axiom status

| Theorem | Standard | Leaf axiom | `sorryAx` (spec stub) |
|---------|----------|------------|-----------------------|
| L7.1 `compute_As_plus_e_fc`     | ✓ | — | — (fully clean) |
| L7.2 `compute_vector_u_fc`      | ✓ | **A1** `sample_matrix_entry_fc` | `Spec.sample_matrix_A_pure` |
| L7.3 `compute_ring_element_v_fc`| ✓ | **A2** `deserialize_to_reduced_ring_element_fc` | `Spec.t_as_ntt_from_public_key_pure` |
| L7.4 `compute_message_fc`       | ✓ | — | — (fully clean) |

### The two deferred-leaf axioms (A1 / A2)

Stated in [`BitMlKem/L7/Axioms.lean`](BitMlKem/L7/Axioms.lean). Both are
`@[spec]` Triples whose statements are **byte-identical** to what the
eventual proofs will establish (so a future session can promote them to
theorems without weakening any downstream proof):

- **A1 `sample_matrix_entry_fc`** — characterizes one on-the-fly matrix
  entry: running the impl's XOF + rejection-sampling chain on `(seed, i, j)`
  produces the `(i, j)` entry of `lift_matrix_from_seed seed K` (row-major),
  with every coefficient in `[0, 3328]`. *Why deferred:* the XOF /
  rejection-sampling semantics are orthogonal to the matrix arithmetic L7.2
  exercises (est. 400–800 LOC to close).

- **A2 `deserialize_to_reduced_ring_element_fc`** — characterizes one
  384-byte public-key chunk: running the impl's 16-iteration
  `deserialize_12 + cond_subtract_3329` loop on chunk `i` produces
  `(lift_t_as_ntt_from_public_key public_key K).val[i]!`, coefficients in
  `[0, 3328]`. *Why deferred:* the 12-bit unpacking + Barrett-equivalent
  canonicalization is mechanical-but-large and orthogonal to L7.3's
  NTT-multiply core (est. 200–400 LOC to close).

### The two spec-layer stubs (`sorryAx`)

The hacspec-side projections referenced by A1/A2 —
`Spec.sample_matrix_A_pure` ([`FCTargets.lean:219`](BitMlKem/FCTargets.lean#L219))
and `Spec.t_as_ntt_from_public_key_pure`
([`FCTargets.lean:271`](BitMlKem/FCTargets.lean#L271)) — currently have
`sorry` bodies. Because they appear in the *statements* of L7.2/L7.3,
those theorems inherit `sorryAx` **structurally from the statement, not
from a proof gap** (the proof bodies contain zero `sorry` tactics). They
must be defined concurrently with promoting A1/A2.

These four items (A1, A2, and the two stubs) are the **only** trust
delta beyond the standard Lean axioms, and they are the two remaining
`sorry`s in the entire tree. Their elimination is the natural next
campaign (see `BitMlKem/L7/Axioms.lean` "Elimination plan").

## Proof architecture

### The lift bridge

The impl works over `PortableVector`-backed `i16`/`i32` coefficients in
the (signed, possibly non-canonical) **Montgomery** domain; the hacspec
works over `parameters.FieldElement` (a `u16` wrapping `ZMod 3329`). The
lift family (in [`BitMlKem/FCTargets.lean`](BitMlKem/FCTargets.lean))
maps impl values to canonical spec values:

- `lift_poly`  — one 256-coefficient ring element.
- `lift_vec` / `lift_vec_slice` — a `K`-vector of ring elements (array / slice).
- `lift_matrix_from_slice` — a stored `K×K` matrix (L7.1).
- `lift_matrix_from_seed` — the sampled matrix (L7.2, via A1 / `sample_matrix_A_pure`).
- `lift_t_as_ntt_from_public_key` — the deserialized `t̂` vector (L7.3, via A2 / `t_as_ntt_from_public_key_pure`).

### Cross-spec Montgomery `R`-factor reconciliation (`scaleZ`)

Impl and hacspec disagree by per-lane Montgomery `R = 2¹⁶ mod 3329`
factors at each arithmetic seam (multiply introduces `R`, the
inverse-NTT a fixed `1/128` scaling, etc.). Rather than hide these in the
lift, each factor is carried **explicitly** as a per-lane scaling
`scaleZ (c : ZMod 3329)`
([`BitMlKem/L7/Correctness/Bridges.lean`](BitMlKem/L7/Correctness/Bridges.lean)),
composed via `scaleZ_compose` and `decide`-checked glue identities
(`3303·2285 ≡ 512`, `1441·169 ≡ 512`, `169·2285 ≡ 1`). Each seam's factor
is pinned by a computable per-contract property-based test **before** any
proof is attempted — see the `#guard`-locked seam-validation files under
[`BitMlKem/L7/Tests/`](BitMlKem/L7/Tests/). For L7.3 the chain is

```
multiply_vectors t̂ r̂  = scaleZ 2285 (lift result1)          -- inner product (R)
ntt_inverse (·)        = scaleZ 512  (lift result2)          -- C ∘ B ∘ glue (3303·2285)
add_polys(add_polys(scaleZ 512 r2, e₂), msg)
                       = add_message_error_reduce_pure …     -- tail, factor 1
```

### FC obligation hierarchy (L0 → L7)

[`BitMlKem/FCTargets.lean`](BitMlKem/FCTargets.lean) is the single locked
statement of the whole bottom-up FC hierarchy (35 theorems). Each layer's
`@[spec]` Triple is consumed by the next via mvcgen / manual
`triple_exists_ok_fc` chaining:

| Layer | Count | Content |
|-------|-------|---------|
| **L0** | 4  | field-element arithmetic (`add`/`sub`/`mul`/`barrett`-reduce in `ZMod 3329`) |
| **L1** | 10 | per-vector-element ops (the `PortableVector` lane primitives) |
| **L2** | 5  | NTT butterfly layer steps (forward + inverse) |
| **L3** | 4  | NTT drivers (full forward/inverse NTT over the 7 layers) |
| **L6** | 6  | poly-level ops: barrett-reduce, subtract-reduce, add-error-reduce, add-message-error-reduce, reducing-from-`i32`-array |
| **L7** | 4  | the matrix-level targets above |

(Plus two Phase-6c scaffolds: L2.8 NTT-multiply vector base case, L6.3 the
polynomial wrapper.)

### The L7 bridge tree

Because the L7 hacspec POSTs differ from their impl walks by the
`scaleZ` factors, each L7 target factors into three files under
[`BitMlKem/L7/`](BitMlKem/L7/):

- `Impl/<Op>.lean`        — the impl-side loop FC(s) + the `scaleZ`-factored
  accumulator bridge (e.g. `multiply_vectors … = scaleZ 2285 …`).
- `Correctness/<Op>.lean` — the pure `ZMod 3329` algebra bridges
  (`scaleZ`, the inverse-NTT linearity `B`/`C`, the add/subtract tail bridges).
- `FC/<Op>.lean`          — the top theorem: walks the impl via
  `triple_exists_ok_fc`, then assembles the hacspec chain from the bridges.

`L7/Common.lean` holds shared scaffolding; `L7/Axioms.lean` the two leaf
axioms; `L7/Tests/` the `#guard`-locked seam validations.

A note on the L7.3 loop: `compute_ring_element_v` deserializes the public
key by iterating a `core_models.iter.adapters.enumerate.Enumerate
(core_models.slice.iter.ChunksExact U8)` via the `loop` combinator. This
loop shape had no Hoare spec in the tree, so L7.3 introduces a reusable
keystone `loop_chunks_exact_pk_spec` (and a generic
`loop_chunks_exact_enumerate_spec`) in
[`BitMlKem/L7/Impl/ComputeRingElementV.lean`](BitMlKem/L7/Impl/ComputeRingElementV.lean),
mirroring `Util/LoopSpecs.lean`'s `loop_range_spec_usize`. It depends on a
faithful `ChunksExact::next` iteration model in the pinned
`rust-core-models` (`FunsExternal.lean`).

### Mathlib isolation barrier

Mathlib is confined to the [`Util/`](Util/) layer (`ModularArith`,
`Montgomery`, `BvMasks`, …). Code above the barrier (`BitMlKem/*`) is
Mathlib-free and reaches `ZMod 3329` only through the mediated `Util/`
lemmas. This keeps the FC layer's elaboration tractable and the
dependency surface auditable.

## File map

```
LibcruxIotMlKem/
├── README.md                       ← you are here
│
├── BitMlKem/
│   ├── Spec.lean                   ← pure-Lean ML-KEM spec hooks (Spec.ntt,
│   │                                 Spec.multiply_ntts, Spec.lift_poly, …)
│   ├── SpecPure.lean               ← the four FE scalar ops + Canonical predicate
│   ├── Commute.lean / StateIso.lean / AlgEquiv.lean
│   │                               ← lift ↔ spec commutation + algebraic equivs
│   ├── FCTargets.lean              ← THE locked FC obligation hierarchy (L0→L7,
│   │                                 35 Triples) + the lift tower; L7.1 proven
│   │                                 in-file; L7.2/3/4 wired to L7/FC/ (see below)
│   └── L7/                         ← matrix-level (L7) bridge tree
│       ├── Axioms.lean             ← A1 sample_matrix_entry_fc,
│       │                             A2 deserialize_to_reduced_ring_element_fc
│       ├── Common.lean             ← shared L7 scaffolding (zero-acc seed, mont-strip bridge)
│       ├── Impl/
│       │   ├── ComputeMessage.lean       ← L7.4 loop FC + acc-bridge
│       │   ├── ComputeVectorU.lean       ← L7.2 loop0/loop1 FC + acc-bridge
│       │   └── ComputeRingElementV.lean  ← L7.3 chunks-exact loop keystone +
│       │                                   deserialize/accumulate FC + acc-bridge
│       ├── Correctness/
│       │   ├── Bridges.lean              ← scaleZ, scaleZ_compose, decide-checked glue
│       │   ├── ComputeMessage.lean       ← L7.4 B/C inverse-NTT linearity + subtract bridge
│       │   ├── ComputeVectorU.lean       ← L7.2 add_polynomials_scaleZ_eq + column bridges
│       │   └── ComputeRingElementV.lean  ← L7.3 D′ two-add tail bridge
│       ├── FC/
│       │   ├── ComputeMessage.lean       ← L7.4 compute_message_fc  (top theorem)
│       │   ├── ComputeVectorU.lean       ← L7.2 compute_vector_u_fc  (top theorem)
│       │   └── ComputeRingElementV.lean  ← L7.3 compute_ring_element_v_fc (top theorem)
│       └── Tests/                  ← #guard-locked per-seam R-factor validations
│
├── Equivalence/                    ← older bottom-up layer proofs (L0–L6 bounds/equiv)
│   └── L0_FieldArith … L6_PolyOps.lean
│
├── Util/                           ← Mathlib isolation barrier
│   ├── ModularArith.lean / Montgomery.lean   ← ZMod 3329 mediated lemmas
│   ├── LoopSpecs.lean              ← loop_range_spec_usize / _i32 (range-loop Hoare specs)
│   ├── CreateI.lean                ← createi_pure_eq (from_fn pure-closure reduction)
│   ├── SliceSpecs.lean / PortableVector.lean / BvMasks.lean / NumericKeystones.lean
│   └── AutomationSandbox.lean
│
└── Extraction/
    └── Funs.lean                   ← Rust impl extraction (generated; do not edit)
```

## Verifying

From `libcrux-iot/ml-kem/proofs/aeneas-lean/`:

```bash
lake exe cache get          # one-time prime
lake build LibcruxIotMlKem  # full tree (≈ 8200 build jobs)
```

Expected: the only `sorry`s in the tree are the **two** spec-layer stubs
`Spec.sample_matrix_A_pure` (`FCTargets.lean:219`) and
`Spec.t_as_ntt_from_public_key_pure` (`FCTargets.lean:271`). Count them
(stripping comments — never `grep -c sorry`, which matches docstrings):

```bash
perl -0777 -pe 's{/-.*?-/}{}gs; s{--[^\n]*}{}g' \
  LibcruxIotMlKem/BitMlKem/FCTargets.lean | grep -oE '\bsorry\b' | wc -l   # → 2
```

Axiom check (`#print axioms <thm>` in an importing file, after a green
`lake build` to avoid stale `.olean` reads):

- `compute_As_plus_e_fc`, `compute_message_fc` → `{propext, Classical.choice, Quot.sound}`.
- `compute_vector_u_fc` → the same + `sample_matrix_entry_fc` + `sorryAx`.
- `compute_ring_element_v_fc` → the same + `deserialize_to_reduced_ring_element_fc` + `sorryAx`.

The `sample_matrix_entry_fc` / `deserialize_to_reduced_ring_element_fc`
entries are the deferred-leaf axioms; the `sorryAx` is the spec-stub
inherited through the statement (see [Assumptions](#assumptions-trust-boundary)).
