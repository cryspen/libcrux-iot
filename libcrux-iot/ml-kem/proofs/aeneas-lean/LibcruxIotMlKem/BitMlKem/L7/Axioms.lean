/-
  # `BitMlKem/L7/Axioms.lean` — L7.2/7.3 deferred-leaf axioms.

  ## Why this file exists

  The L7.2 (`compute_vector_u_fc`) and L7.3 (`compute_ring_element_v_fc`)
  hacspec POSTs reference projections — `lift_matrix_from_seed seed K` and
  `lift_t_as_ntt_from_public_key public_key K` respectively — that require
  connecting impl-side **on-the-fly matrix sampling** and **public-key
  deserialization** to their pure-projection counterparts in FCTargets.lean.

  Per the pivot plan §"L7.2-L7.4 disciplined pivot"
  (`~/.claude/plans/iot-mlkem-l72-l74-pivot-plan-2026-05-28.md`) §3.3
  contract audit deliverable (`~/.claude/plans/iot-mlkem-l0-l6-contract-audit.md`)
  identified these as **M1** and **M2** — two missing leaf FC theorems
  whose full proofs would require ~600-1200 LOC of XOF / rejection-sampling /
  Barrett-deserialize machinery.

  We **temporarily axiomatize** them so L7.2 and L7.3 main theorems
  (and their loop helpers) can close *conditionally* on these axioms.
  This trades ~600-1200 LOC of unrelated downstream work for **two named,
  byte-locked axioms** that future sessions can promote to full proofs
  via the `lean4:axiom-eliminator` agent — the project's established
  scaffold-then-eliminate pattern.

  ## Discipline

  - Each axiom statement is byte-identical to what the eventual `@[spec]
    theorem ... := by ...` will prove. **Do not weaken** an axiom's
    statement to make a downstream proof easier; if a downstream proof
    needs a stronger axiom, that's the signal that the axiom shape is
    wrong, not the downstream proof.
  - Both axioms have `@[spec]` so they are picked up by the mvcgen-driven
    Triple chaining the same way the eventual theorems will be.
  - Tracked in the campaign ledger as deferred obligations. `lean_verify`
    on any L7.2 / L7.3 main theorem will list these axioms in its output,
    keeping the trust boundary explicit.
  - The PRE and POST bounds were derived from impl-body inspection
    (see § per-axiom comments below) — they are NOT placeholders.

  ## Elimination plan

  - **A1 `sample_matrix_entry_fc`**: replace with a full `theorem` body
    that traces the impl's XOF / rejection-sampling chain through
    `sampling.sample_from_xof` and `PolynomialRingElement.from_i16_array`,
    establishing the per-entry equation to `lift_matrix_from_seed`'s
    `(j, i)` projection. Estimated 400-800 LOC. Requires concurrent
    closure of `Spec.sample_matrix_A_pure`'s currently-sorry body in
    `FCTargets.lean:219`.
  - **A2 `deserialize_to_reduced_ring_element_fc`**: replace with a
    full `theorem` body that traces the 16-iteration `deserialize_12 +
    cond_subtract_3329` chunk loop. Estimated 200-400 LOC. Requires
    concurrent closure of `Spec.t_as_ntt_from_public_key_pure`'s
    sorry body in `FCTargets.lean:271`.

  ## What L7.2/L7.3 will look like with these axioms

  - L7.2 `compute_vector_u_fc`: the proof's loop helpers (M3/M4/M5 per
    audit §3.3) invoke `sample_matrix_entry_fc` inside their step
    lemmas to connect impl-side per-iteration samples to the canonical
    matrix-from-seed projection. The K=2 grand equation (Phase 0c)
    will reference these axioms by name.
  - L7.3 `compute_ring_element_v_fc`: the loop helper (M6) invokes
    `deserialize_to_reduced_ring_element_fc` per public-key chunk.

  L7.4 `compute_message_fc` requires **no axiom** from this file — its
  hacspec POST references only `lift_poly`, `lift_vec`. It will close
  unconditionally.
-/

import LibcruxIotMlKem.BitMlKem.FCTargets

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace libcrux_iot_ml_kem.BitMlKem.FCTargets

open Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.BitMlKem

/-! ## §A1 `sample_matrix_entry_fc` — deferred leaf FC for L7.2

    ### Impl shape (Extraction/Funs.lean:796)

    ```
    def matrix.sample_matrix_entry
      {Vector : Type} {Hasher : Type}
      (vectortraitsOperationsInst : vector.traits.Operations Vector)
      (hash_functionsHashInst : hash_functions.Hash Hasher)
      (out : polynomial.PolynomialRingElement Vector)
      (seed : Slice Std.U8) (i : Std.Usize) (j : Std.Usize) :
      Result (polynomial.PolynomialRingElement Vector)
    ```

    Body: prepends `(i, j)` to the 32-byte seed, runs `sample_from_xof`
    (rejection sampling on uniform [0, 2^12-1)), then `from_i16_array`
    into `out`. Result has |coeff| ≤ 3328 (rejection sampling discards
    values ≥ 3329).

    ### Why an axiom

    The XOF + rejection-sampling chain is orthogonal to the matrix-arithmetic
    core that L7.2 actually exercises. Closing the chain requires
    `Spec.sample_matrix_A_pure`'s body (currently `sorry` in
    `FCTargets.lean:219`) to be defined in terms of the hacspec spec's
    own sampling logic, plus a per-coefficient projection lemma — all of
    which is XOF semantics, not L7.2 matrix arithmetic.

    ### Statement (ROW-major access via `lift_matrix_from_seed`)

    **NB — differs from L7.1's `matrix.entry_fc` convention.** L7.1
    `compute_As_plus_e` calls `multiply_matrix_by_column a_as_ntt s`
    *without* transposing, so its column-major lift accesses
    `.val[j]!.val[i]!`. L7.2 `compute_vector_u`, by contrast, computes
    `multiply_matrix_by_column (transpose a_as_ntt) r` — the extra
    `transpose` flips the effective convention, so the (i-th row,
    j-th column) entry the impl samples via `sample_matrix_entry seed i j`
    must land at `(lift_matrix_from_seed seed K).val[i.val]!.val[j.val]!`
    (ROW-major). Verified by computable check (2026-05-29): hacspec
    `multiply_matrix_by_column_at (transpose A) r i = multiply_vectors
    A.val[i] r` (row-major), so FC requires `lift(sample i j) =
    LM.val[i]!.val[j]!`. The earlier column-major statement (copied from
    `matrix.entry_fc`) was transposed-wrong for L7.2 and would have made
    `compute_vector_u_fc` false for asymmetric matrices. -/
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

    ### Impl shape (Extraction/Funs.lean:1345)

    ```
    def serialize.deserialize_to_reduced_ring_element
      {Vector : Type}
      (vectortraitsOperationsInst : vector.traits.Operations Vector)
      (serialized : Slice Std.U8)
      (re : polynomial.PolynomialRingElement Vector) :
      Result (polynomial.PolynomialRingElement Vector)
    ```

    Body: 16-iteration loop over 24-byte sub-chunks of `serialized`
    (one `BYTES_PER_RING_ELEMENT = 384` byte ring-element). Each chunk
    extracts 16 packed 12-bit coefficients via `deserialize_12`, then
    `cond_subtract_3329` produces canonical residues [0, 3328].
    So each output lane is in [0, 3328], hence |coeff| ≤ 3328.

    ### Why an axiom

    The chunk-level bit-shifting / packing semantics + the per-chunk
    Barrett-equivalent cond_subtract is mechanical-but-large and orthogonal
    to L7.3's NTT-multiply core. Closing it requires
    `Spec.t_as_ntt_from_public_key_pure`'s body (currently `sorry` in
    `FCTargets.lean:271`) to be defined in terms of hacspec's
    deserialization, plus a per-chunk projection lemma.

    ### Statement

    The axiom asserts that running the impl on a single ring-element-sized
    slice of the public key produces the matching index of the
    `lift_t_as_ntt_from_public_key` projection. L7.3's loop helper (M6)
    will compose K such instances to cover the entire public key.

    The `i` index threads the impl's `chunks_exact` iterator position
    (0 ≤ i < K), matching the impl-side enumerate loop in
    `compute_ring_element_v_loop` (Extraction/Funs.lean:1495). -/
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
