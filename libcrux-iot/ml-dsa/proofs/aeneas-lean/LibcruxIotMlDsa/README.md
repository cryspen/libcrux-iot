# ML-DSA `PolynomialRingElement` layer: impl ↔ spec equivalence

This directory contains the Lean 4 proof that the Rust implementation of
ML-DSA's **`PolynomialRingElement<SIMDUnit>` API** and its supporting
per-SIMD-unit arithmetic in `libcrux-iot/ml-dsa/src/` computes the same functions
as the ML-DSA specification in `specs/ml-dsa` (q = 8 380 417). **Both sides are
machine-extracted** to aeneas-lean by the `cargo hax into aeneas-lean` pipeline:
the impl from `libcrux-iot/ml-dsa/src/`, the spec from the `hacspec_ml_dsa` crate
(the `HacspecMlDsa` dependency). The top-level theorems state that each impl
function matches its `hacspec_ml_dsa.*` counterpart — no hand-written reference is
trusted.

Every theorem below is **axiom-clean** — it depends only on Lean's three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and **no** leaf
axioms. The whole tree builds green; the only `sorry`s are in the upstream
Aeneas `Std` library, none in this development or in the extraction.

> **Two implementation bugs were found and fixed during this verification** (both
> in `simd/portable/arithmetic.rs`, a checked→wrapping-ops conversion slip):
> `reduce_element` and `infinity_norm_exceeds` had `wrapping_sub` where
> `wrapping_mul` was meant. The latter is security-relevant (the signing
> rejection check). Both are fixed in the impl history; the proofs are against
> the corrected code.

## The extracted `Operations<Coefficients>` instance

The `PolynomialRingElement` / `ntt` API is generic over the
`simd::traits::Operations` trait. The whole layer is dispatched through a single
concrete instance, `Operations Coefficients`, which is **emitted by the
extraction** (not hand-written): see
[`Polynomial/Ntt.lean`](Polynomial/Ntt.lean)'s `portable_ops_inst`, an
abbreviation for the aeneas-generated
`…vector_type.Coefficients.Insts.…SimdTraitsOperations`. Every top-level theorem
applies the generic impl function at this instance, so the proofs cover exactly
the code that ships.

## Top-level theorems — the `PolynomialRingElement` API

Each is an `mvcgen` Triple `⦃ True ⦄ <impl> portable_ops_inst args… ⦃ ⇓ r => ⌜ <post> ⌝ ⦄`
that ties the impl function directly to its counterpart in the extracted spec
`hacspec_ml_dsa.*`. The impl stores coefficients as 32 SIMD units × 8 signed,
Montgomery-domain `i32` lanes; **`lift_poly_res`** ([`Spec/HacspecBridge.lean`](Spec/HacspecBridge.lean))
re-encodes them as the spec's representation — a flat canonical-residue `[i32; 256]`,
Montgomery factor stripped lane-wise.

Representative statement ([`Polynomial/HacspecNtt.lean`](Polynomial/HacspecNtt.lean)):

```lean
theorem ntt_hacspec_fc (re : PolynomialRingElement Coefficients) (B : Nat)
    (hB : …) (hin : …per-lane bound B…) :
    ⦃ ⌜ True ⌝ ⦄
    ntt.ntt portable_ops_inst re
    ⦃ ⇓ r => ⌜ hacspec_ml_dsa.ntt.ntt (lift_poly_res re) = .ok (lift_poly_res r) ⌝ ⦄
```

| Theorem (file) | impl function | extracted-spec post |
|---|---|---|
| `ntt_hacspec_fc` ([`Polynomial/HacspecNtt.lean`](Polynomial/HacspecNtt.lean)) | `ntt.ntt` | `hacspec_ml_dsa.ntt.ntt (lift_poly_res re) = .ok (lift_poly_res r)` |
| `intt_hacspec_fc` ([`Polynomial/HacspecNtt.lean`](Polynomial/HacspecNtt.lean)) | `ntt.invert_ntt_montgomery` | `hacspec_ml_dsa.ntt.intt (lift_poly_res re) = .ok (lift_poly_res_intt r)`¹ |
| `poly_pointwise_mul_hacspec_fc` ([`Polynomial/HacspecFC.lean`](Polynomial/HacspecFC.lean)) | `ntt.ntt_multiply_montgomery` | `hacspec_ml_dsa.polynomial.poly_pointwise_mul (lift_poly_res lhs) (lift_poly_res rhs) = .ok (lift_poly_res r)` |
| `poly_add_hacspec_fc` ([`Polynomial/HacspecFC.lean`](Polynomial/HacspecFC.lean)) | `…PolynomialRingElement.add` | `hacspec_ml_dsa.polynomial.poly_add (lift_poly_res self) (lift_poly_res rhs) = .ok (lift_poly_res r)` |
| `poly_sub_hacspec_fc` ([`Polynomial/HacspecFC.lean`](Polynomial/HacspecFC.lean)) | `…PolynomialRingElement.subtract` | `hacspec_ml_dsa.polynomial.poly_sub (lift_poly_res self) (lift_poly_res rhs) = .ok (lift_poly_res r)` |
| `infinity_norm_exceeds_hacspec_fc` ([`Polynomial/HacspecNorm.lean`](Polynomial/HacspecNorm.lean)) | `…PolynomialRingElement.infinity_norm_exceeds` | `r = decide (bound ≤ poly_infinity_norm (canon_raw self))`² |

¹ The impl's inverse NTT leaves its output in the Montgomery domain (`· R`);
`lift_poly_res_intt` strips that factor (`· R⁻¹`) so the result matches the
extracted `intt`.
² Centering precond — see the representation note below.

Four impl ops have no non-trivial counterpart in the spec (it treats them as
identity / a constant / a copy), so they are stated as direct value equations:

| Theorem (file) | impl function | post |
|---|---|---|
| `reduce_fc` ([`Polynomial/NttArith.lean`](Polynomial/NttArith.lean)) | `ntt.reduce` | `lift_poly r = lift_poly re` (Barrett-reduce; residues unchanged) |
| `zero_fc` ([`Polynomial/Convert.lean`](Polynomial/Convert.lean)) | `…zero` | `lift_poly r = 0` (the zero polynomial) |
| `to_i32_array_fc` ([`Polynomial/Convert.lean`](Polynomial/Convert.lean)) | `…to_i32_array` | `∀ k<256, (r[k]).val =` self coefficient `k` |
| `from_i32_array_fc` ([`Polynomial/Convert.lean`](Polynomial/Convert.lean)) | `…from_i32_array` | `∀ k<256,` r coefficient `k` `= (array[k]).val` |

### How the equivalence is established

`hacspec_ml_dsa.*` is the `specs/ml-dsa` Rust spec crate machine-extracted to
aeneas-lean (the same pipeline as the impl), wired in as the `HacspecMlDsa` Lake
dependency. The bridge ([`Spec/HacspecBridge.lean`](Spec/HacspecBridge.lean))
re-encodes between the impl's SIMD lanes and the spec's `[i32; 256]`, proves the
extracted `mod_q` total and residue-preserving (`mod_q_eq`), and matches each
extracted op to the impl; the `ZETAS`-table match (`zetas_bridge`) is a kernel
`decide` in `Z_q` over the full 256-entry table. Internally the equivalence
factors through a clean-`Z_q` Lean restatement
([`Spec/Pure.lean`](Spec/Pure.lean), proven equal to the extracted spec) — a
proof convenience that keeps the algebra in `ZMod q`, not a separately trusted
artifact.

> **Representation note (`infinity_norm_exceeds`).** The impl computes the raw
> signed `|coefficient|`; the spec's `coeff_norm`/`poly_infinity_norm` compute the
> centered FIPS norm. These coincide when each coefficient is a centered
> representative (`|·| ≤ (q−1)/2`), which the FIPS signing context guarantees; the
> connection FC carries an explicit `hcentered` hypothesis.

## Supporting layers

The top-level theorems are corollaries / loop-compositions of a stack of proven
per-SIMD-unit and NTT-driver results. None depend on non-standard axioms.

### NTT masters (the per-array `[Coefficients; 32]` engines)

| Theorem (file) | impl function |
|---|---|
| `ntt_inner_fc` ([`Vector/Portable/NttMaster.lean`](Vector/Portable/NttMaster.lean)) | `simd.portable.ntt.ntt` (8 forward layers) |
| `invert_ntt_inner_fc` ([`Vector/Portable/InvNttMaster.lean`](Vector/Portable/InvNttMaster.lean)) | `simd.portable.invntt.invert_ntt_montgomery` (8 inverse layers + finalize) |

These compose the per-layer butterfly drivers
([`Vector/Portable/{Ntt,InvNtt,NttDriver,InvNttDriver}.lean`](Vector/Portable/)).

### Per-SIMD-unit (8-lane) arithmetic and rounding

| Theorem (file) | impl function |
|---|---|
| `montgomery_reduce_element_spec` ([`Vector/Portable/Arithmetic.lean`](Vector/Portable/Arithmetic.lean)) | `montgomery_reduce_element` |
| `reduce_element_spec` ([`Vector/Portable/Arithmetic.lean`](Vector/Portable/Arithmetic.lean)) | `reduce_element` (Barrett) |
| `add_spec` / `subtract_spec` / `montgomery_multiply_spec` / `montgomery_multiply_by_constant_spec` ([`Vector/Portable/Element.lean`](Vector/Portable/Element.lean)) | `arithmetic.{add,subtract,montgomery_multiply,montgomery_multiply_by_constant}` |
| `zero_unit_spec` / `to_coefficient_array_spec` / `from_coefficient_array_spec` ([`Vector/Portable/Element.lean`](Vector/Portable/Element.lean)) | `vector_type.{zero,to_coefficient_array,from_coefficient_array}` |
| `shift_left_then_reduce_spec` ([`Vector/Portable/Arithmetic.lean`](Vector/Portable/Arithmetic.lean)) | `shift_left_then_reduce` |
| `infinity_norm_exceeds_unit_spec` ([`Vector/Portable/Arithmetic.lean`](Vector/Portable/Arithmetic.lean)) | `arithmetic.infinity_norm_exceeds` (the bug-fixed sign-mask) |
| `power2round_spec` / `decompose_spec` / `use_hint_spec` / `compute_hint_spec` ([`Vector/Portable/Rounding.lean`](Vector/Portable/Rounding.lean)) | FIPS-204 §7.4 rounding |

## Assumptions (trust boundary)

What is **trusted** rather than **proven** in this directory:

- **Standard Lean axioms only** — `propext`, `Classical.choice`, `Quot.sound`.
  No leaf/sampling/serialization axioms are used (every theorem here is
  `#print axioms`-clean against the standard three).
- **Out of scope (kept `opaque` in the extraction):** the matrix-level pipelines
  (`matrix.compute_as1_plus_s2`, `compute_matrix_x_mask`), the
  sampling/encoding/serialization modules (`sample`, `encoding`,
  `hash_functions`, `samplex4`), and the top-level `ml_dsa_generic` driver. These
  are signature-only in the extraction (a hax mutable-slice-iterator limitation,
  [hax #720], for the matrix/vector wrappers) and are not part of this layer's
  proof. The per-SIMD-unit versions of the vector rounding wrappers
  (`power2round`, `decompose`) *are* verified (see the rounding row above); only
  the 32-unit vector maps over them are opaque.
- **Spec faithfulness** — the reference is the machine-**extracted** `specs/ml-dsa`
  Rust spec (`HacspecMlDsa`): the same Rust source the F\*/test artifacts use,
  extracted by the same `cargo hax` pipeline. The trust assumption is that this
  extraction faithfully reflects the Rust source — no hand-written spec is
  trusted. The `Spec/Pure.lean` restatement is proven equal to the extraction,
  and build-time `#guard`s in [`Spec/Validation.lean`](Spec/Validation.lean)
  independently check it against the Rust `ZETAS` table, the NTT round-trip, and
  rounding boundary invariants.

## Proof architecture

The impl works over `Coefficients`-backed `i32` lanes in the (signed,
non-canonical) **Montgomery** domain, packed as 32 SIMD units of 8 lanes. The
proofs reduce these lane-wise to a clean `Array (ZMod q)` of 256 coefficients —
the working representation in which the algebra is done (the spec's own
`[i32; 256]` is its canonical-residue image). The lift family in
[`Spec/Lift.lean`](Spec/Lift.lean):

- `liftZ x = (x : Z_q) · R⁻¹` (strips one Montgomery factor); `liftZ_std x = (x : Z_q)`.
- `lift_units` / `lift_poly` flatten 32×8 lanes into a 256-element `Z_q` poly,
  mont-stripped lane-wise (`lift_poly re = lift_units re.simd_units`, by `rfl`).
- Seam lemmas: `liftZ_add`/`liftZ_sub` (additivity), `liftZ_of_mont`
  (a Montgomery product lifts to a clean product — the `R⁻¹²` reconciliation
  used by `ntt_multiply_montgomery_fc`).

The poly-layer proofs are either one-step corollaries of the NTT masters
(`ntt`, `invert_ntt_montgomery`) or 32-unit loop compositions of the per-unit
specs (`add`, `subtract`, `ntt_multiply_montgomery`, `reduce`, `zero`,
`to_i32_array`, `from_i32_array`, `infinity_norm_exceeds`), driven by the loop
combinators in [`Util/`](Util/).

## Reproduction

### Verifying the Lean proof

Lean toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.30.0-rc2`).
From `libcrux-iot/ml-dsa/proofs/aeneas-lean/`:

```bash
lake exe cache get
lake build LibcruxIotMlDsa
```

### Re-extracting from Rust

The extraction is driven by `libcrux-iot/ml-dsa/hax_aeneas.py` (hax-evit toolchain
+ pinned charon/aeneas; see the ML-KEM tree's README for the exact pinned
versions). It regenerates `Extraction/Funs.lean`. The `Operations<Coefficients>`
instance is retained via a `#[cfg(hax_backend_lean)]` verification-only anchor in
`src/ntt.rs` (`_portable_operations_anchor`) — the sole reachable monomorphic
user of the trait at `Coefficients`, never compiled into the shipped library.

[hax #720]: https://github.com/hacspec/hax/issues/720
