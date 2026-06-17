/-
  # `BitMlKem/L7/Axioms.lean` — L7.2/7.3 deferred-leaf axioms.

  ## Why this file exists

  We verify the matrix operations without verifying the underlying
  **sampling** and **public-key deserialization**.

-/

import LibcruxIotMlKem.BitMlKem.FCTargets

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace libcrux_iot_ml_kem.BitMlKem.FCTargets

open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.BitMlKem

/-! ## §A1 `sample_matrix_entry_fc` — deferred leaf FC for L7.2

    prepends `(i, j)` to the 32-byte seed, runs `sample_from_xof`
    (rejection sampling on uniform [0, 2^12-1)), then `from_i16_array`
    into `out`. Result has |coeff| ≤ 3328 (rejection sampling discards
    values ≥ 3329).
-/
@[spec]
axiom sample_matrix_entry_fc
    {Hasher : Type}
    (hash_functionsHashInst : libcrux_iot_ml_kem.hash_functions.Hash Hasher)
    (out : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (seed : Slice Std.U8) (i j K : Std.Usize)
    (h_seed_len : seed.length = 32)
    (h_i : i.val < K.val) (h_j : j.val < K.val) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.matrix.sample_matrix_entry
      (vectortraitsOperationsInst := portable_ops_inst)
      hash_functionsHashInst out seed i j
    ⦃ ⇓ p => ⌜ lift_poly p = (lift_matrix_from_seed seed K).val[i.val]!.val[j.val]!
                ∧ (∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
                    ((p.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 3328) ⌝ ⦄

/-! ## §A2 `deserialize_to_reduced_ring_element_fc` — deferred leaf FC for L7.3

    16-iteration loop over 24-byte sub-chunks of `serialized`
    (one `BYTES_PER_RING_ELEMENT = 384` byte ring-element). Each chunk
    extracts 16 packed 12-bit coefficients via `deserialize_12`, then
    `cond_subtract_3329` produces canonical residues [0, 3328].
    So each output lane is in [0, 3328], hence |coeff| ≤ 3328.
-/
@[spec]
axiom deserialize_to_reduced_ring_element_fc
    (public_key : Slice Std.U8) (K : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (i : Std.Usize)
    (h_pk_len : public_key.length = K.val * 384)
    (h_i : i.val < K.val)
    (chunk_bytes : Slice Std.U8)
    (h_chunk_len : chunk_bytes.length = 384)
    (h_chunk_eq : ∀ ℓ : Nat, ℓ < 384 →
        chunk_bytes.val[ℓ]! = public_key.val[i.val * 384 + ℓ]!) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.serialize.deserialize_to_reduced_ring_element
      (vectortraitsOperationsInst := portable_ops_inst)
      chunk_bytes re
    ⦃ ⇓ p => ⌜ lift_poly p = (lift_t_as_ntt_from_public_key public_key K).val[i.val]!
                ∧ (∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
                    ((p.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 3328) ⌝ ⦄

end libcrux_iot_ml_kem.BitMlKem.FCTargets
