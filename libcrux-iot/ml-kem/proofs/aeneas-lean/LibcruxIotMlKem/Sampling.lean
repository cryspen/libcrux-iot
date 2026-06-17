/-
  # `Sampling.lean` — deferred leaf FC axiom for matrix sampling.

  We verify the matrix operations without verifying the underlying
  rejection sampling. `sample_matrix_entry_fc` axiomatises the contract
  that the impl `matrix.sample_matrix_entry` implements
  `Spec.sample_matrix_A_pure`'s `(i, j)`-th entry with canonical
  coefficients.
-/

import LibcruxIotMlKem.FCTargets

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace libcrux_iot_ml_kem.BitMlKem.FCTargets

open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.BitMlKem

/-- prepends `(i, j)` to the 32-byte seed, runs `sample_from_xof`
    (rejection sampling on uniform [0, 2^12-1)), then `from_i16_array`
    into `out`. Result has |coeff| ≤ 3328 (rejection sampling discards
    values ≥ 3329). -/
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

end libcrux_iot_ml_kem.BitMlKem.FCTargets
