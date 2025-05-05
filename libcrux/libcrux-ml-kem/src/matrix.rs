use crate::{
    hash_functions::Hash, helper::cloop, invert_ntt::invert_ntt_montgomery,
    polynomial::PolynomialRingElement, sampling::sample_from_xof, vector::Operations,
};

#[inline(always)]
pub(crate) fn entry<const K: usize, Vector: Operations>(
    matrix: &[PolynomialRingElement<Vector>],
    i: usize,
    j: usize,
) -> &PolynomialRingElement<Vector> {
    debug_assert!(matrix.len() == K * K);
    debug_assert!(i < K);
    debug_assert!(j < K);
    &matrix[i * K + j]
}

#[inline(always)]
pub(crate) fn entry_mut<const K: usize, Vector: Operations>(
    matrix: &mut [PolynomialRingElement<Vector>],
    i: usize,
    j: usize,
) -> &mut PolynomialRingElement<Vector> {
    debug_assert!(matrix.len() == K * K);
    debug_assert!(i < K);
    debug_assert!(j < K);
    &mut matrix[i * K + j]
}

#[inline(always)]
#[allow(non_snake_case)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K"#))]
#[hax_lib::ensures(|res|
    fstar!(r#"let (matrix_A, valid) = Spec.MLKEM.sample_matrix_A_ntt (Seq.slice $seed 0 32) in
        valid ==> (
        if $transpose then Libcrux_ml_kem.Polynomial.to_spec_matrix_t ${A_transpose}_future == matrix_A
        else Libcrux_ml_kem.Polynomial.to_spec_matrix_t ${A_transpose}_future == Spec.MLKEM.matrix_transpose matrix_A)"#)
)]
pub(crate) fn sample_matrix_A<const K: usize, Vector: Operations, Hasher: Hash>(
    A_transpose: &mut [PolynomialRingElement<Vector>],
    seed: [u8; 34],
    transpose: bool,
) {
    debug_assert!(A_transpose.len() == K * K);

    for i in 0..K {
        let mut seeds = [seed; K];
        for j in 0..K {
            seeds[j][32] = i as u8;
            seeds[j][33] = j as u8;
        }
        let mut sampled_coefficients = [0usize; K];
        let mut out = [[0i16; 272]; K];
        sample_from_xof::<K, Vector, Hasher>(&seeds, &mut sampled_coefficients, &mut out);
        cloop! {
            for (j, sample) in out.into_iter().enumerate() {
                // A[i][j] = A_transpose[j][i]
                if transpose {
                    PolynomialRingElement::from_i16_array(&sample[..256], entry_mut::<K, Vector>(A_transpose, j,i));
                } else {
                    PolynomialRingElement::from_i16_array(&sample[..256], entry_mut::<K, Vector>(A_transpose, i, j)); // XXX: in this case we might want to copy all of sample at once
                }
            }
        }
    }
    ()
}

/// The following functions compute various expressions involving
/// vectors and matrices. The computation of these expressions has been
/// abstracted away into these functions in order to save on loop iterations.

/// Compute v − InverseNTT(sᵀ ◦ NTT(u))
#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K"#))]
#[hax_lib::ensures(|res|
    fstar!(r#"let open Libcrux_ml_kem.Polynomial in
        let secret_spec = to_spec_vector_t $secret_as_ntt in
        let u_spec = to_spec_vector_t $u_as_ntt in
        let v_spec = to_spec_poly_t $v in
        to_spec_poly_t $res ==
            Spec.MLKEM.(poly_sub v_spec (poly_inv_ntt (vector_dot_product_ntt #$K secret_spec u_spec))) /\
        Libcrux_ml_kem.Serialize.coefficients_field_modulus_range $res"#)
)]
pub(crate) fn compute_message<const K: usize, Vector: Operations>(
    v: &PolynomialRingElement<Vector>,
    secret_as_ntt: &[PolynomialRingElement<Vector>; K],
    u_as_ntt: &[PolynomialRingElement<Vector>; K],
    result: &mut PolynomialRingElement<Vector>,
    scratch: &mut PolynomialRingElement<Vector>,
) {
    for i in 0..K {
        secret_as_ntt[i].ntt_multiply(&u_as_ntt[i], scratch);
        result.add_to_ring_element::<K>(scratch);
    }

    invert_ntt_montgomery::<K, Vector>(result, &mut scratch.coefficients[0]);
    v.subtract_reduce(result);
}

/// Compute InverseNTT(tᵀ ◦ r̂) + e₂ + message
#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K"#))]
#[hax_lib::ensures(|res|
    fstar!(r#"let open Libcrux_ml_kem.Polynomial in
        let tt_spec = to_spec_vector_t $t_as_ntt in
        let r_spec = to_spec_vector_t $r_as_ntt in
        let e2_spec = to_spec_poly_t $error_2 in
        let m_spec = to_spec_poly_t $message in
        let res_spec = to_spec_poly_t $res in
        res_spec == Spec.MLKEM.(poly_add (poly_add (vector_dot_product_ntt #$K tt_spec r_spec) e2_spec) m_spec) /\
        Libcrux_ml_kem.Serialize.coefficients_field_modulus_range $res"#)
)]
pub(crate) fn compute_ring_element_v<const K: usize, Vector: Operations>(
    t_as_ntt: &[PolynomialRingElement<Vector>; K],
    r_as_ntt: &[PolynomialRingElement<Vector>],
    error_2: &PolynomialRingElement<Vector>,
    message: &PolynomialRingElement<Vector>,
    result: &mut PolynomialRingElement<Vector>,
    scratch: &mut PolynomialRingElement<Vector>,
    cache: &[PolynomialRingElement<Vector>],
) {
    for i in 0..K {
        t_as_ntt[i].ntt_multiply_cached(&r_as_ntt[i], scratch, &cache[i]);
        result.add_to_ring_element::<K>(&scratch);
    }

    invert_ntt_montgomery::<K, Vector>(result, &mut scratch.coefficients[0]);
    error_2.add_message_error_reduce(message, result, &mut scratch.coefficients[0]);
}

/// Compute u := InvertNTT(Aᵀ ◦ r̂) + e₁
#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K"#))]
#[hax_lib::ensures(|res|
    fstar!(r#"let open Libcrux_ml_kem.Polynomial in
        let a_spec = to_spec_matrix_t $a_as_ntt in
        let r_spec = to_spec_vector_t $r_as_ntt in
        let e_spec = to_spec_vector_t $error_1 in
        let res_spec = to_spec_vector_t $res in
        res_spec == Spec.MLKEM.(vector_add (vector_inv_ntt (matrix_vector_mul_ntt a_spec r_spec)) e_spec) /\
        (forall (i:nat). i < v $K ==>
            Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index $res i))"#)
)]
pub(crate) fn compute_vector_u<const K: usize, Vector: Operations>(
    a_as_ntt: &[PolynomialRingElement<Vector>],
    r_as_ntt: &[PolynomialRingElement<Vector>],
    cache: &mut [PolynomialRingElement<Vector>],
    error_1: &[PolynomialRingElement<Vector>],
    result: &mut [PolynomialRingElement<Vector>],
    scratch: &mut PolynomialRingElement<Vector>,
) {
    debug_assert!(a_as_ntt.len() == K * K);
    debug_assert!(r_as_ntt.len() == K);
    debug_assert!(error_1.len() == K);

    for j in 0..K {
        entry::<K, Vector>(a_as_ntt, 0, j).ntt_multiply_caching(
            &r_as_ntt[j],
            scratch,
            &mut cache[j],
        );
        result[0].add_to_ring_element::<K>(scratch);
    }

    invert_ntt_montgomery::<K, Vector>(&mut result[0], &mut scratch.coefficients[0]);
    result[0].add_error_reduce(&error_1[0]);

    for i in 1..K {
        for j in 0..K {
            entry::<K, Vector>(a_as_ntt, i, j).ntt_multiply_cached(
                &r_as_ntt[j],
                scratch,
                &cache[j],
            );
            result[i].add_to_ring_element::<K>(scratch);
        }

        invert_ntt_montgomery::<K, Vector>(&mut result[i], &mut scratch.coefficients[0]);
        result[i].add_error_reduce(&error_1[i]);
    }
}

/// Compute Â ◦ ŝ + ê
#[inline(always)]
#[allow(non_snake_case)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K"#))]
#[hax_lib::ensures(|res|
    fstar!(r#"let open Libcrux_ml_kem.Polynomial in
        to_spec_vector_t ${t_as_ntt}_future =
             Spec.MLKEM.compute_As_plus_e_ntt
               (to_spec_matrix_t $matrix_A) 
               (to_spec_vector_t $s_as_ntt) 
               (to_spec_vector_t $error_as_ntt) /\
        (forall (i: nat). i < v $K ==>
            Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index ${t_as_ntt}_future i))"#)
)]
pub(crate) fn compute_As_plus_e<const K: usize, Vector: Operations>(
    t_as_ntt: &mut [PolynomialRingElement<Vector>; K],
    matrix_A: &[PolynomialRingElement<Vector>],
    s_as_ntt: &[PolynomialRingElement<Vector>; K],
    error_as_ntt: &[PolynomialRingElement<Vector>; K],
    scratch: &mut PolynomialRingElement<Vector>,
) {
    // During the first row of multiplications, we build up the cache
    // of intermediate values.
    t_as_ntt[0] = PolynomialRingElement::<Vector>::ZERO();
    let mut s_cache = [PolynomialRingElement::<Vector>::ZERO(); K];
    for j in 0..K {
        entry::<K, Vector>(matrix_A, 0, j).ntt_multiply_caching(
            &s_as_ntt[j],
            scratch,
            &mut s_cache[j],
        );
        t_as_ntt[0].add_to_ring_element::<K>(scratch);
    }
    t_as_ntt[0].add_standard_error_reduce(&error_as_ntt[0]);

    // The remaining rows can re-use the cached intermediate values.
    for i in 1..K {
        // This may be externally provided memory. Ensure that `t_as_ntt`
        // is all 0.
        t_as_ntt[i] = PolynomialRingElement::<Vector>::ZERO();

        for j in 0..K {
            entry::<K, Vector>(matrix_A, i, j).ntt_multiply_cached(
                &s_as_ntt[j],
                scratch,
                &s_cache[j],
            );
            t_as_ntt[i].add_to_ring_element::<K>(scratch);
        }
        t_as_ntt[i].add_standard_error_reduce(&error_as_ntt[i]);
    }

    ()
}
