# ML-DSA `PolynomialRingElement` layer: impl ↔ spec equivalence

This directory contains the Lean 4 proof that the Rust implementation of
ML-DSA's **`PolynomialRingElement<SIMDUnit>` API** and its supporting
per-SIMD-unit arithmetic in `libcrux-iot/ml-dsa/src/` computes the same
functions as a clean-`Z_q` (q = 8 380 417) hacspec-style reference. The impl is
auto-extracted via the `cargo hax into aeneas-lean` pipeline; this directory then
proves functional-correctness (FC) equivalence against a pure Lean spec
(`Spec/Pure.lean`, mirroring `specs/ml-dsa`).

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

Each is an `mvcgen` Triple of the form
`⦃ True ⦄ <impl> portable_ops_inst args… ⦃ ⇓ r => ⌜ <post over lift_poly r> ⌝ ⦄`,
linking the extracted impl to the pure spec through the **`lift_poly`** bridge
(`Spec/Lift.lean`): `lift_poly` strips the Montgomery factor (`· R⁻¹`) lane-wise
and flattens the 32 SIMD units × 8 lanes into a flat 256-coefficient `Z_q`
polynomial. (The `infinity_norm_exceeds` post is at a different altitude — raw
signed-integer magnitudes — since it is a norm check, not a `Z_q` computation.)

Representative statement ([`Polynomial/Ntt.lean`](Polynomial/Ntt.lean)):

```lean
theorem ntt_fc (re : PolynomialRingElement Coefficients) (B : Nat)
    (hB : (B : Int) + 34 * 2 ^ 24 ≤ 2 ^ 31 - 1) (hin : …per-lane bound B…) :
    ⦃ ⌜ True ⌝ ⦄
    ntt.ntt portable_ops_inst re
    ⦃ ⇓ r => ⌜ lift_poly r = Pure.ntt (lift_poly re) ∧ …output bound… ⌝ ⦄
```

| Theorem (file) | impl function | post (functional core) |
|---|---|---|
| `ntt_fc` ([`Polynomial/Ntt.lean`](Polynomial/Ntt.lean)) | `ntt.ntt` | `lift_poly r = Pure.ntt (lift_poly re)` |
| `invert_ntt_montgomery_fc` ([`Polynomial/Ntt.lean`](Polynomial/Ntt.lean)) | `ntt.invert_ntt_montgomery` | `lift_poly r = (Pure.intt (lift_poly re)).map (·*R)` |
| `ntt_multiply_montgomery_fc` ([`Polynomial/NttArith.lean`](Polynomial/NttArith.lean)) | `ntt.ntt_multiply_montgomery` | `lift_poly r = Pure.poly_pointwise_mul (lift_poly lhs) (lift_poly rhs)` |
| `reduce_fc` ([`Polynomial/NttArith.lean`](Polynomial/NttArith.lean)) | `ntt.reduce` | `lift_poly r = lift_poly re` (Barrett-reduce; residues unchanged) |
| `add_fc` ([`Polynomial/Arithmetic.lean`](Polynomial/Arithmetic.lean)) | `…PolynomialRingElement.add` | `lift_poly r = Pure.poly_add (lift_poly self) (lift_poly rhs)` |
| `subtract_fc` ([`Polynomial/Arithmetic.lean`](Polynomial/Arithmetic.lean)) | `…PolynomialRingElement.subtract` | `lift_poly r = Pure.poly_sub (lift_poly self) (lift_poly rhs)` |
| `zero_fc` ([`Polynomial/Convert.lean`](Polynomial/Convert.lean)) | `…PolynomialRingElement.zero` | `lift_poly r = Pure.zero_poly` |
| `to_i32_array_fc` ([`Polynomial/Convert.lean`](Polynomial/Convert.lean)) | `…PolynomialRingElement.to_i32_array` | `∀ k<256, (r[k]).val =` self's coefficient `k` |
| `from_i32_array_fc` ([`Polynomial/Convert.lean`](Polynomial/Convert.lean)) | `…PolynomialRingElement.from_i32_array` | `∀ k<256,` r's coefficient `k` `= (array[k]).val` |
| `infinity_norm_exceeds_fc` ([`Polynomial/InfinityNorm.lean`](Polynomial/InfinityNorm.lean)) | `…PolynomialRingElement.infinity_norm_exceeds` | `r = decide (Spec.Pure.infinity_norm_exceeds coeffs bound)` |

`from_i32_array_fc` additionally has a `lift_poly`-form corollary
`from_i32_array_lift_fc`.

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
- **Spec faithfulness** — `Spec/Pure.lean` is trusted to match the FIPS-204 /
  `specs/ml-dsa` reference; it is cross-checked at build time by the `#guard`s in
  [`Spec/Validation.lean`](Spec/Validation.lean) (NTT round-trip, the Rust
  `ZETAS` table, rounding reconstruction/boundary invariants, ∞-norm agreement).

## Proof architecture

The impl works over `Coefficients`-backed `i32` lanes in the (signed,
non-canonical) **Montgomery** domain, packed as 32 SIMD units of 8 lanes; the
spec works over a flat `Array (ZMod q)` of 256 canonical coefficients. The lift
family in [`Spec/Lift.lean`](Spec/Lift.lean) bridges them:

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
