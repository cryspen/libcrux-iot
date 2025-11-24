use super::arithmetic::*;
use super::vector_type::*;
use libcrux_secrets::*;

#[inline(always)]
#[hax_lib::fstar::before("[@@ \"opaque_to_smt\"]")]
#[hax_lib::requires(fstar!(r#"v i < 16 /\ v j < 16 /\ v i <> v j /\ 
                            Spec.Utils.is_i16b 1664 $zeta  /\
                            Spec.Utils.is_i16b_array (11207 + 6 * 3328) vec.f_elements /\
                            Spec.Utils.is_i16b (11207 + 5*3328) vec.f_elements.[i] /\
                            Spec.Utils.is_i16b (11207 + 5*3328) vec.f_elements.[j]"#))]
#[hax_lib::ensures(|_| fstar!(r#"(forall k. (k <> v i /\ k <> v j) ==>
                                         Seq.index ${vec}_future.f_elements k == Seq.index ${vec}.f_elements k) /\
                                    (forall b. (Spec.Utils.is_i16b b ${vec}.f_elements.[i] /\
                                               Spec.Utils.is_i16b b ${vec}.f_elements.[j]) ==>
                                              (Spec.Utils.is_i16b (b+3328) ${vec}_future.f_elements.[i] /\
                                               Spec.Utils.is_i16b (b+3328) ${vec}_future.f_elements.[j])) /\
                                    Spec.Utils.ntt_spec ${vec}.f_elements (v $zeta) (v $i) (v $j) ${vec}_future.f_elements"#))]
pub(crate) fn ntt_step(vec: &mut PortableVector, zeta: i16, i: usize, j: usize) {
    let t = montgomery_multiply_fe_by_fer(vec.elements[j], zeta.classify());
    hax_lib::fstar!(
        "assert (v t % 3329 == ((v (Seq.index vec.f_elements (v j)) * v zeta * 169) % 3329))"
    );
    let a_minus_t = vec.elements[i] - t;
    hax_lib::fstar!(
        r#"
    calc (==) {
        v $a_minus_t % 3329;
        (==) {}
        (v (Seq.index vec.f_elements (v i)) - v ${t}) % 3329;
        (==) {Math.Lemmas.lemma_mod_sub_distr (v (Seq.index vec.f_elements (v $i))) (v $t) 3329}
        (v (Seq.index vec.f_elements (v $i)) - (v $t % 3329)) % 3329;
        (==) {}
        (v (Seq.index vec.f_elements (v i)) - ((v (Seq.index vec.f_elements (v $j)) * v $zeta * 169) % 3329)) % 3329;
        (==) {Math.Lemmas.lemma_mod_sub_distr (v (Seq.index vec.f_elements (v $i))) (v (Seq.index vec.f_elements (v $j)) * v zeta * 169) 3329}
        (v (Seq.index vec.f_elements (v $i)) - (v (Seq.index vec.f_elements (v $j)) * v $zeta * 169)) % 3329;
        }"#
    );
    let a_plus_t = vec.elements[i] + t;
    hax_lib::fstar!(
        r#"
    calc (==) {
        v a_plus_t % 3329;
        (==) {}
        (v (Seq.index vec.f_elements (v $i)) + v $t) % 3329;
        (==) {Math.Lemmas.lemma_mod_add_distr (v (Seq.index vec.f_elements (v $i))) (v $t) 3329}
        (v (Seq.index vec.f_elements (v $i)) + (v $t % 3329)) % 3329;
        (==) {}
        (v (Seq.index vec.f_elements (v $i)) + ((v (Seq.index vec.f_elements (v $j)) * v $zeta * 169) % 3329)) % 3329;
        (==) {Math.Lemmas.lemma_mod_add_distr (v (Seq.index vec.f_elements (v $i))) (v (Seq.index vec.f_elements (v $j)) * v zeta * 169) 3329}
        (v (Seq.index vec.f_elements (v $i)) + (v (Seq.index vec.f_elements (v $j)) * v $zeta * 169)) % 3329;
    }"#
    );
    vec.elements[j] = a_minus_t;
    vec.elements[i] = a_plus_t;
    hax_lib::fstar!(
        "assert (Seq.index vec.f_elements (v i) == a_plus_t);
                     assert (Seq.index vec.f_elements (v j) == a_minus_t)"
    );
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 100")]
#[hax_lib::requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
                            Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
                            Spec.Utils.is_i16b_array (11207+5*3328) ${vec}.f_elements"#))]
#[hax_lib::ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array (11207+6*3328) ${vec}_future.f_elements"#))]
pub(crate) fn ntt_layer_1_step(
    vec: &mut PortableVector,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) {
    ntt_step(vec, zeta0, 0, 2);
    ntt_step(vec, zeta0, 1, 3);
    ntt_step(vec, zeta1, 4, 6);
    ntt_step(vec, zeta1, 5, 7);
    ntt_step(vec, zeta2, 8, 10);
    ntt_step(vec, zeta2, 9, 11);
    ntt_step(vec, zeta3, 12, 14);
    ntt_step(vec, zeta3, 13, 15);
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 100")]
#[hax_lib::requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
                            Spec.Utils.is_i16b_array (11207+4*3328) ${vec}.f_elements"#))]
#[hax_lib::ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array (11207+5*3328) ${vec}_future.f_elements"#))]
pub(crate) fn ntt_layer_2_step(vec: &mut PortableVector, zeta0: i16, zeta1: i16) {
    ntt_step(vec, zeta0, 0, 4);
    ntt_step(vec, zeta0, 1, 5);
    ntt_step(vec, zeta0, 2, 6);
    ntt_step(vec, zeta0, 3, 7);
    ntt_step(vec, zeta1, 8, 12);
    ntt_step(vec, zeta1, 9, 13);
    ntt_step(vec, zeta1, 10, 14);
    ntt_step(vec, zeta1, 11, 15);
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 100")]
#[hax_lib::requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta /\
                            Spec.Utils.is_i16b_array (11207+3*3328) ${vec}.f_elements"#))]
#[hax_lib::ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array (11207+4*3328) ${vec}_future.f_elements"#))]
pub(crate) fn ntt_layer_3_step(vec: &mut PortableVector, zeta: i16) {
    ntt_step(vec, zeta, 0, 8);
    ntt_step(vec, zeta, 1, 9);
    ntt_step(vec, zeta, 2, 10);
    ntt_step(vec, zeta, 3, 11);
    ntt_step(vec, zeta, 4, 12);
    ntt_step(vec, zeta, 5, 13);
    ntt_step(vec, zeta, 6, 14);
    ntt_step(vec, zeta, 7, 15);
}

#[inline(always)]
#[hax_lib::fstar::before("[@@ \"opaque_to_smt\"]")]
#[hax_lib::requires(fstar!(r#"v i < 16 /\ v j < 16 /\  v i <> v j /\ 
                        Spec.Utils.is_i16b 1664 $zeta /\
                        Spec.Utils.is_i16b_array (4*3328) ${vec}.f_elements"#))]
#[hax_lib::ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array (4*3328) ${vec}_future.f_elements /\
                                    (forall k. (k <> v i /\ k <> v j) ==>
                                         Seq.index ${vec}_future.f_elements k == Seq.index ${vec}.f_elements k) /\
                                    Spec.Utils.is_i16b 3328 (Seq.index ${vec}_future.f_elements (v i)) /\
                                    Spec.Utils.is_i16b 3328 (Seq.index ${vec}_future.f_elements (v j)) /\
                                    Spec.Utils.inv_ntt_spec ${vec}.f_elements (v $zeta) (v $i) (v $j) ${vec}_future.f_elements"#))]
pub(crate) fn inv_ntt_step(vec: &mut PortableVector, zeta: i16, i: usize, j: usize) {
    let a_minus_b = vec.elements[j] - vec.elements[i];
    let a_plus_b = vec.elements[j] + vec.elements[i];
    hax_lib::fstar!(
        r#"assert (v a_minus_b = v (Seq.index vec.f_elements (v j)) - v (Seq.index vec.f_elements (v i)));
                     assert (v a_plus_b = v (Seq.index vec.f_elements (v j)) + v (Seq.index vec.f_elements (v i)))"#
    );
    let o0 = barrett_reduce_element(a_plus_b);
    let o1 = montgomery_multiply_fe_by_fer(a_minus_b, zeta.classify());
    hax_lib::fstar!(
        r#"
    calc (==) {
        v o0 % 3329;
        (==) { }
        v a_plus_b % 3329;
        (==) { }
        (v (Seq.index vec.f_elements (v j)) + v (Seq.index vec.f_elements (v i))) % 3329;
    };
    calc (==) {
        v o1 % 3329;
        (==) { }
        (v a_minus_b * v zeta * 169) % 3329;
        (==) { }
        ((v (Seq.index vec.f_elements (v j)) - v (Seq.index vec.f_elements (v i))) * v zeta * 169) % 3329;
    }"#
    );
    vec.elements[i] = o0;
    vec.elements[j] = o1;
    hax_lib::fstar!(
        r#"assert (Seq.index vec.f_elements (v i) == o0);
                     assert (Seq.index vec.f_elements (v j) == o1)"#
    );
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 200")]
#[hax_lib::requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
                            Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
                            Spec.Utils.is_i16b_array (4*3328) ${vec}.f_elements"#))]
#[hax_lib::ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array 3328 ${vec}_future.f_elements"#))]
pub(crate) fn inv_ntt_layer_1_step(
    vec: &mut PortableVector,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) {
    inv_ntt_step(vec, zeta0, 0, 2);
    inv_ntt_step(vec, zeta0, 1, 3);
    inv_ntt_step(vec, zeta1, 4, 6);
    inv_ntt_step(vec, zeta1, 5, 7);
    inv_ntt_step(vec, zeta2, 8, 10);
    inv_ntt_step(vec, zeta2, 9, 11);
    inv_ntt_step(vec, zeta3, 12, 14);
    inv_ntt_step(vec, zeta3, 13, 15);
    hax_lib::fstar!(
        r#"assert (Spec.Utils.is_i16b 3328 (Seq.index ${vec}.f_elements 13));
        assert (Spec.Utils.is_i16b 3328 (Seq.index ${vec}.f_elements 15));
        assert (Spec.Utils.is_i16b 3328 (Seq.index ${vec}.f_elements 12));
        assert (Spec.Utils.is_i16b 3328 (Seq.index ${vec}.f_elements 14));
        assert (Spec.Utils.is_i16b 3328 (Seq.index ${vec}.f_elements 9));
        assert (Spec.Utils.is_i16b 3328 (Seq.index ${vec}.f_elements 11));
        assert (Spec.Utils.is_i16b 3328 (Seq.index ${vec}.f_elements 8));
        assert (Spec.Utils.is_i16b 3328 (Seq.index ${vec}.f_elements 10));
        assert (Spec.Utils.is_i16b 3328 (Seq.index ${vec}.f_elements 5));
        assert (Spec.Utils.is_i16b 3328 (Seq.index ${vec}.f_elements 7));
        assert (Spec.Utils.is_i16b 3328 (Seq.index ${vec}.f_elements 4));
        assert (Spec.Utils.is_i16b 3328 (Seq.index ${vec}.f_elements 6));
        assert (Spec.Utils.is_i16b 3328 (Seq.index ${vec}.f_elements 1));
        assert (Spec.Utils.is_i16b 3328 (Seq.index ${vec}.f_elements 3));
        assert (Spec.Utils.is_i16b 3328 (Seq.index ${vec}.f_elements 0));
        assert (Spec.Utils.is_i16b 3328 (Seq.index ${vec}.f_elements 2));
        assert (forall (i:nat). i < 16 ==> Spec.Utils.is_i16b 3328 (Seq.index ${vec}.f_elements i))"#
    );
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 100")]
#[hax_lib::requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
                            Spec.Utils.is_i16b_array 3328 ${vec}.f_elements"#))]
#[hax_lib::ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array 3328 ${vec}_future.f_elements"#))]
pub(crate) fn inv_ntt_layer_2_step(vec: &mut PortableVector, zeta0: i16, zeta1: i16) {
    inv_ntt_step(vec, zeta0, 0, 4);
    inv_ntt_step(vec, zeta0, 1, 5);
    inv_ntt_step(vec, zeta0, 2, 6);
    inv_ntt_step(vec, zeta0, 3, 7);
    inv_ntt_step(vec, zeta1, 8, 12);
    inv_ntt_step(vec, zeta1, 9, 13);
    inv_ntt_step(vec, zeta1, 10, 14);
    inv_ntt_step(vec, zeta1, 11, 15);
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 100")]
#[hax_lib::requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta /\
                            Spec.Utils.is_i16b_array 3328 ${vec}.f_elements"#))]
#[hax_lib::ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array 3328 ${vec}_future.f_elements"#))]
pub(crate) fn inv_ntt_layer_3_step(vec: &mut PortableVector, zeta: i16) {
    inv_ntt_step(vec, zeta, 0, 8);
    inv_ntt_step(vec, zeta, 1, 9);
    inv_ntt_step(vec, zeta, 2, 10);
    inv_ntt_step(vec, zeta, 3, 11);
    inv_ntt_step(vec, zeta, 4, 12);
    inv_ntt_step(vec, zeta, 5, 13);
    inv_ntt_step(vec, zeta, 6, 14);
    inv_ntt_step(vec, zeta, 7, 15);
}

/// Compute the product of two Kyber binomials with respect to the
/// modulus `X² - zeta`.
///
/// This function almost implements <strong>Algorithm 11</strong> of the
/// NIST FIPS 203 standard, which is reproduced below:
///
/// ```plaintext
/// Input:  a₀, a₁, b₀, b₁ ∈ ℤq.
/// Input: γ ∈ ℤq.
/// Output: c₀, c₁ ∈ ℤq.
///
/// c₀ ← a₀·b₀ + a₁·b₁·γ
/// c₁ ← a₀·b₁ + a₁·b₀
/// return c₀, c₁
/// ```
/// We say "almost" because the coefficients output by this function are in
/// the Montgomery domain (unlike in the specification).
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
#[inline(always)]
#[hax_lib::fstar::options(
    "--z3rlimit 250 --split_queries always --query_stats --ext context_prune"
)]
#[hax_lib::fstar::before(interface, "[@@ \"opaque_to_smt\"]")]
#[hax_lib::requires(fstar!(r#"v i < 8 /\ Spec.Utils.is_i16b 1664 $zeta /\
        Spec.Utils.is_i16b_array 3328 ${a}.f_elements /\
        Spec.Utils.is_i16b_array 3328 ${b}.f_elements /\
        Spec.Utils.is_i16b_array 3328 ${out}.f_elements "#))]
#[hax_lib::ensures(|()| fstar!(r#"
        Spec.Utils.is_i16b_array 3328 ${out}_future.f_elements /\
        (forall k. (k <> 2 * v $i /\ k <> 2 * v $i + 1) ==> 
                    Seq.index ${out}_future.f_elements k == Seq.index ${out}.f_elements k) /\                 
        (let ai = Seq.index ${a}.f_elements (2 * v $i) in
         let aj = Seq.index ${a}.f_elements (2 * v $i + 1) in
         let bi = Seq.index ${b}.f_elements (2 * v $i) in
         let bj = Seq.index ${b}.f_elements (2 * v $i + 1) in
         let oi = Seq.index out_future.f_elements (2 * v $i) in
         let oj = Seq.index out_future.f_elements (2 * v $i + 1) in
         ((v oi % 3329) == (((v ai * v bi + (v aj * v bj * v zeta * 169)) * 169) % 3329)) /\
         ((v oj % 3329) == (((v ai * v bj + v aj * v bi) * 169) % 3329)))"#))]
pub(crate) fn accumulating_ntt_multiply_binomials_fill_cache(
    a: &PortableVector,
    b: &PortableVector,
    zeta: FieldElementTimesMontgomeryR,
    i: usize,
    out: &mut [I32],
    cache: &mut PortableVector,
) {
    let ai = a.elements[2 * i];
    let bi = b.elements[2 * i];
    let aj = a.elements[2 * i + 1];
    let bj = b.elements[2 * i + 1];

    let ai_bi = (ai.as_i32()) * (bi.as_i32());
    let bj_zeta_ = (bj.as_i32()) * (zeta.as_i32());
    let bj_zeta = montgomery_reduce_element(bj_zeta_);
    cache.elements[i] = bj_zeta;
    let aj_bj_zeta = (aj.as_i32()) * (bj_zeta.as_i32());
    let ai_bi_aj_bj = ai_bi + aj_bj_zeta;
    let o0 = ai_bi_aj_bj;

    let ai_bj = (ai.as_i32()) * (bj.as_i32());
    let aj_bi = (aj.as_i32()) * (bi.as_i32());
    let ai_bj_aj_bi = ai_bj + aj_bi;
    let o1 = ai_bj_aj_bi;

    out[2 * i] += o0;
    out[2 * i + 1] += o1;
}

#[inline(always)]
pub(crate) fn accumulating_ntt_multiply_binomials_use_cache(
    a: &PortableVector,
    b: &PortableVector,
    i: usize,
    out: &mut [I32],
    cache: &PortableVector,
) {
    let ai = a.elements[2 * i];
    let bi = b.elements[2 * i];
    let aj = a.elements[2 * i + 1];
    let bj = b.elements[2 * i + 1];

    let ai_bi = (ai.as_i32()) * (bi.as_i32());
    let aj_bj_zeta = (aj.as_i32()) * (cache.elements[i].as_i32());
    let ai_bi_aj_bj = ai_bi + aj_bj_zeta;
    let o0 = ai_bi_aj_bj;

    let ai_bj = (ai.as_i32()) * (bj.as_i32());
    let aj_bi = (aj.as_i32()) * (bi.as_i32());
    let ai_bj_aj_bi = ai_bj + aj_bi;
    let o1 = ai_bj_aj_bi;

    out[2 * i] += o0;
    out[2 * i + 1] += o1;
}

#[inline(always)]
pub(crate) fn accumulating_ntt_multiply_binomials(
    a: &PortableVector,
    b: &PortableVector,
    zeta: FieldElementTimesMontgomeryR,
    i: usize,
    out: &mut [I32],
) {
    let ai = a.elements[2 * i];
    let bi = b.elements[2 * i];
    let aj = a.elements[2 * i + 1];
    let bj = b.elements[2 * i + 1];

    let ai_bi = (ai.as_i32()) * (bi.as_i32());
    let bj_zeta_ = (bj.as_i32()) * (zeta.as_i32());
    let bj_zeta = montgomery_reduce_element(bj_zeta_);
    let aj_bj_zeta = (aj.as_i32()) * (bj_zeta.as_i32());
    let ai_bi_aj_bj = ai_bi + aj_bj_zeta;
    let o0 = ai_bi_aj_bj;

    let ai_bj = (ai.as_i32()) * (bj.as_i32());
    let aj_bi = (aj.as_i32()) * (bi.as_i32());
    let ai_bj_aj_bi = ai_bj + aj_bi;
    let o1 = ai_bj_aj_bi;

    out[2 * i] += o0;
    out[2 * i + 1] += o1;
}

#[inline(always)]
pub(crate) fn accumulating_ntt_multiply(
    lhs: &PortableVector,
    rhs: &PortableVector,
    out: &mut [I32],
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) {
    let nzeta0 = -zeta0;
    let nzeta1 = -zeta1;
    let nzeta2 = -zeta2;
    let nzeta3 = -zeta3;
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b 1664 nzeta0)"#);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b 1664 nzeta1)"#);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b 1664 nzeta2)"#);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b 1664 nzeta3)"#);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b_array 3328 out.f_elements)"#);
    accumulating_ntt_multiply_binomials(lhs, rhs, zeta0.classify(), 0, out);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b_array 3328 out.f_elements)"#);
    accumulating_ntt_multiply_binomials(lhs, rhs, nzeta0.classify(), 1, out);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b_array 3328 out.f_elements)"#);
    accumulating_ntt_multiply_binomials(lhs, rhs, zeta1.classify(), 2, out);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b_array 3328 out.f_elements)"#);
    accumulating_ntt_multiply_binomials(lhs, rhs, nzeta1.classify(), 3, out);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b_array 3328 out.f_elements)"#);
    accumulating_ntt_multiply_binomials(lhs, rhs, zeta2.classify(), 4, out);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b_array 3328 out.f_elements)"#);
    accumulating_ntt_multiply_binomials(lhs, rhs, nzeta2.classify(), 5, out);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b_array 3328 out.f_elements)"#);
    accumulating_ntt_multiply_binomials(lhs, rhs, zeta3.classify(), 6, out);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b_array 3328 out.f_elements)"#);
    accumulating_ntt_multiply_binomials(lhs, rhs, nzeta3.classify(), 7, out);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b_array 3328 out.f_elements)"#);
}

#[inline(always)]
pub(crate) fn accumulating_ntt_multiply_fill_cache(
    lhs: &PortableVector,
    rhs: &PortableVector,
    out: &mut [I32],
    cache: &mut PortableVector,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) {
    let nzeta0 = -zeta0;
    let nzeta1 = -zeta1;
    let nzeta2 = -zeta2;
    let nzeta3 = -zeta3;
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b 1664 nzeta0)"#);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b 1664 nzeta1)"#);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b 1664 nzeta2)"#);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b 1664 nzeta3)"#);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b_array 3328 out.f_elements)"#);
    accumulating_ntt_multiply_binomials_fill_cache(lhs, rhs, zeta0.classify(), 0, out, cache);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b_array 3328 out.f_elements)"#);
    accumulating_ntt_multiply_binomials_fill_cache(lhs, rhs, nzeta0.classify(), 1, out, cache);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b_array 3328 out.f_elements)"#);
    accumulating_ntt_multiply_binomials_fill_cache(lhs, rhs, zeta1.classify(), 2, out, cache);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b_array 3328 out.f_elements)"#);
    accumulating_ntt_multiply_binomials_fill_cache(lhs, rhs, nzeta1.classify(), 3, out, cache);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b_array 3328 out.f_elements)"#);
    accumulating_ntt_multiply_binomials_fill_cache(lhs, rhs, zeta2.classify(), 4, out, cache);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b_array 3328 out.f_elements)"#);
    accumulating_ntt_multiply_binomials_fill_cache(lhs, rhs, nzeta2.classify(), 5, out, cache);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b_array 3328 out.f_elements)"#);
    accumulating_ntt_multiply_binomials_fill_cache(lhs, rhs, zeta3.classify(), 6, out, cache);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b_array 3328 out.f_elements)"#);
    accumulating_ntt_multiply_binomials_fill_cache(lhs, rhs, nzeta3.classify(), 7, out, cache);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b_array 3328 out.f_elements)"#);
}

#[inline(always)]
pub(crate) fn accumulating_ntt_multiply_use_cache(
    lhs: &PortableVector,
    rhs: &PortableVector,
    out: &mut [I32],
    cache: &PortableVector,
) {
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b 1664 nzeta0)"#);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b 1664 nzeta1)"#);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b 1664 nzeta2)"#);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b 1664 nzeta3)"#);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b_array 3328 out.f_elements)"#);
    accumulating_ntt_multiply_binomials_use_cache(lhs, rhs, 0, out, cache);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b_array 3328 out.f_elements)"#);
    accumulating_ntt_multiply_binomials_use_cache(lhs, rhs, 1, out, cache);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b_array 3328 out.f_elements)"#);
    accumulating_ntt_multiply_binomials_use_cache(lhs, rhs, 2, out, cache);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b_array 3328 out.f_elements)"#);
    accumulating_ntt_multiply_binomials_use_cache(lhs, rhs, 3, out, cache);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b_array 3328 out.f_elements)"#);
    accumulating_ntt_multiply_binomials_use_cache(lhs, rhs, 4, out, cache);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b_array 3328 out.f_elements)"#);
    accumulating_ntt_multiply_binomials_use_cache(lhs, rhs, 5, out, cache);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b_array 3328 out.f_elements)"#);
    accumulating_ntt_multiply_binomials_use_cache(lhs, rhs, 6, out, cache);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b_array 3328 out.f_elements)"#);
    accumulating_ntt_multiply_binomials_use_cache(lhs, rhs, 7, out, cache);
    hax_lib::fstar!(r#"assert (Spec.Utils.is_i16b_array 3328 out.f_elements)"#);
}
