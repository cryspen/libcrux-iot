use libcrux_secrets::{I16, I32, U8};

pub const MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS: i16 = 1353;
pub const FIELD_MODULUS: i16 = 3329;
pub const FIELD_ELEMENTS_IN_VECTOR: usize = 16;
pub const INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u32 = 62209; // FIELD_MODULUS^{-1} mod MONTGOMERY_R
pub const BARRETT_SHIFT: i32 = 26;
pub const BARRETT_R: i32 = 1 << BARRETT_SHIFT;

// We define a trait that allows us to talk about the contents of a vector.
// This is used extensively in pre- and post-conditions to reason about the code.
// The trait is duplicated for Eurydice to avoid the trait inheritance between Operations and Repr
// This is needed because of this issue: https://github.com/AeneasVerif/eurydice/issues/111
#[cfg(hax)]
#[hax_lib::attributes]
pub trait Repr: Copy + Clone {
    #[requires(true)]
    fn repr(&self) -> [i16; 16];
}

#[cfg(any(eurydice, not(hax)))]
pub trait Repr {}

#[cfg(hax)]
pub(crate) mod spec {
    pub(crate) fn add_pre(lhs: &[i16; 16], rhs: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"forall i. i < 16 ==> 
            Spec.Utils.is_intb (pow2 15 - 1) 
                (v (Seq.index ${lhs} i) + v (Seq.index ${rhs} i))"#
        )
    }

    pub(crate) fn add_post(lhs: &[i16; 16], rhs: &[i16; 16], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"forall i. i < 16 ==> 
            (v (Seq.index ${result} i) == 
            v (Seq.index ${lhs} i) + v (Seq.index ${rhs} i))"#
        )
    }

    pub(crate) fn sub_pre(lhs: &[i16; 16], rhs: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"forall i. i < 16 ==> 
            Spec.Utils.is_intb (pow2 15 - 1) 
                (v (Seq.index ${lhs} i) - v (Seq.index ${rhs} i))"#
        )
    }

    pub(crate) fn sub_post(lhs: &[i16; 16], rhs: &[i16; 16], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"forall i. i < 16 ==> 
            (v (Seq.index ${result} i) == 
            v (Seq.index ${lhs} i) - v (Seq.index ${rhs} i))"#
        )
    }

    pub(crate) fn negate_pre(vec: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"forall i. i < 16 ==> 
                Spec.Utils.is_intb (pow2 15 - 1) (v (Seq.index ${vec} i))"#
        )
    }

    pub(crate) fn negate_post(vec: &[i16; 16], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"forall i. i < 16 ==> 
                v (Seq.index ${result} i) == 
                - (v (Seq.index ${vec} i))"#
        )
    }

    pub(crate) fn multiply_by_constant_pre(vec: &[i16; 16], c: i16) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"forall i. i < 16 ==> 
                Spec.Utils.is_intb (pow2 15 - 1) (v (Seq.index ${vec} i) * v $c)"#
        )
    }

    pub(crate) fn multiply_by_constant_post(
        vec: &[i16; 16],
        c: i16,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"forall i.
                v (Seq.index ${result} i) == 
                v (Seq.index ${vec} i) * v $c"#
        )
    }

    pub(crate) fn bitwise_and_with_constant_constant_post(
        vec: &[i16; 16],
        c: i16,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"$result == 
               Spec.Utils.map_array (fun x -> x &. $c) $vec"#
        )
    }

    pub(crate) fn shift_right_post(
        vec: &[i16; 16],
        shift_by: i32,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"(v $shift_by >= 0 /\ v $shift_by < 16) ==>
                $result == 
                Spec.Utils.map_array (fun x -> x >>! ${shift_by}) $vec"#
        )
    }

    pub(crate) fn cond_subtract_3329_pre(vec: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Spec.Utils.is_i16b_array (pow2 12 - 1) $vec"#)
    }

    pub(crate) fn cond_subtract_3329_post(vec: &[i16; 16], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"$result == 
                Spec.Utils.map_array (fun x -> 
                    if x >=. (mk_i16 3329) then 
                        x -! (mk_i16 3329) 
                    else x) $vec"#
        )
    }

    pub(crate) fn barrett_reduce_pre(vec: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Spec.Utils.is_i16b_array 28296 $vec"#)
    }

    pub(crate) fn barrett_reduce_post(vec: &[i16; 16], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"Spec.Utils.is_i16b_array 3328 ${result} /\
                (forall i. (v (Seq.index ${result} i) % 3329) == 
                           (v (Seq.index ${vec} i) % 3329))"#
        )
    }

    pub(crate) fn montgomery_multiply_by_constant_pre(vec: &[i16; 16], c: i16) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Spec.Utils.is_i16b 1664 c"#)
    }

    pub(crate) fn montgomery_multiply_by_constant_post(
        vec: &[i16; 16],
        c: i16,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"Spec.Utils.is_i16b_array 3328 ${result} /\
                (forall i. ((v (Seq.index ${result} i) % 3329)==
                            (v (Seq.index ${vec} i) * v ${c} * 169) % 3329))"#
        )
    }

    pub(crate) fn to_unsigned_representative_pre(vec: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Spec.Utils.is_i16b_array 3328 ${vec}"#)
    }

    pub(crate) fn to_unsigned_representative_post(
        vec: &[i16; 16],
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"forall i.
                let x = Seq.index ${vec} i in
                let y = Seq.index ${result} i in
                (v y >= 0 /\ v y <= 3328 /\ (v y % 3329 == v x % 3329))"#
        )
    }

    pub(crate) fn compress_1_pre(vec: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"forall i. 
                v (Seq.index ${vec} i) >= 0 /\
                v (Seq.index ${vec} i) < 3329"#
        )
    }

    pub(crate) fn compress_1_post(vec: &[i16; 16], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"forall i. bounded (Seq.index ${result} i) 1"#)
    }

    pub(crate) fn compress_pre(vec: &[i16; 16], coefficient_bits: i32) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"(v $coefficient_bits == 4 \/
                v $coefficient_bits == 5 \/
                v $coefficient_bits == 10 \/
                v $coefficient_bits == 11) /\
                (forall i. 
                    v (Seq.index $vec i) >= 0 /\
                    v (Seq.index $vec i) < 3329)"#
        )
    }

    pub(crate) fn compress_post(
        vec: &[i16; 16],
        coefficient_bits: i32,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"(v $coefficient_bits == 4 \/
                v $coefficient_bits == 5 \/
                v $coefficient_bits == 10 \/
                v $coefficient_bits == 11) ==>
                (forall i. bounded (Seq.index ${result} i) (v $coefficient_bits))"#
        )
    }

    pub(crate) fn decompress_1_pre(vec: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"forall i. 
               let x = Seq.index ${vec} i in 
               (x == mk_i16 0 \/ x == mk_i16 1)"#
        )
    }

    pub(crate) fn decompress_ciphertext_coefficient_pre(
        vec: &[i16; 16],
        coefficient_bits: i32,
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"(v $coefficient_bits == 4 \/
                v $coefficient_bits == 5 \/
                v $coefficient_bits == 10 \/
                v $coefficient_bits == 11) /\
                (forall i. 
                    v (Seq.index $vec i) >= 0 /\
                    v (Seq.index $vec i) < pow2 (v $coefficient_bits))"#
        )
    }

    pub(crate) fn ntt_layer_1_step_pre(
        vec: &[i16; 16],
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#" Spec.Utils.is_i16b 1664 $zeta0 /\ Spec.Utils.is_i16b 1664 $zeta1 /\ 
                Spec.Utils.is_i16b 1664 $zeta2 /\ Spec.Utils.is_i16b 1664 $zeta3 /\
                Spec.Utils.is_i16b_array (11207+5*3328) ${vec}"#
        )
    }

    pub(crate) fn ntt_layer_1_step_post(
        vec: &[i16; 16],
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Spec.Utils.is_i16b_array (11207+6*3328) ${result}"#)
    }

    pub(crate) fn ntt_layer_2_step_pre(vec: &[i16; 16], zeta0: i16, zeta1: i16) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#" Spec.Utils.is_i16b 1664 $zeta0 /\ Spec.Utils.is_i16b 1664 $zeta1 /\ 
                Spec.Utils.is_i16b_array (11207+4*3328) ${vec}"#
        )
    }

    pub(crate) fn ntt_layer_2_step_post(
        vec: &[i16; 16],
        zeta0: i16,
        zeta1: i16,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Spec.Utils.is_i16b_array (11207+5*3328) ${result}"#)
    }

    pub(crate) fn ntt_layer_3_step_pre(vec: &[i16; 16], zeta0: i16) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#" Spec.Utils.is_i16b 1664 $zeta0 /\
                Spec.Utils.is_i16b_array (11207+3*3328) ${vec}"#
        )
    }

    pub(crate) fn ntt_layer_3_step_post(
        vec: &[i16; 16],
        zeta0: i16,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Spec.Utils.is_i16b_array (11207+4*3328) ${result}"#)
    }

    pub(crate) fn inv_ntt_layer_1_step_pre(
        vec: &[i16; 16],
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#" Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\ 
                Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
                Spec.Utils.is_i16b_array (4*3328) ${vec}"#
        )
    }

    pub(crate) fn inv_ntt_layer_1_step_post(
        vec: &[i16; 16],
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Spec.Utils.is_i16b_array 3328 ${result}"#)
    }

    pub(crate) fn inv_ntt_layer_2_step_pre(
        vec: &[i16; 16],
        zeta0: i16,
        zeta1: i16,
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#" Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\ 
                Spec.Utils.is_i16b_array 3328 ${vec}"#
        )
    }

    pub(crate) fn inv_ntt_layer_2_step_post(
        vec: &[i16; 16],
        zeta0: i16,
        zeta1: i16,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Spec.Utils.is_i16b_array 3328 ${result}"#)
    }

    pub(crate) fn inv_ntt_layer_3_step_pre(vec: &[i16; 16], zeta0: i16) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#" Spec.Utils.is_i16b 1664 $zeta0 /\
                Spec.Utils.is_i16b_array 3328 ${vec}"#
        )
    }

    pub(crate) fn inv_ntt_layer_3_step_post(
        vec: &[i16; 16],
        zeta0: i16,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Spec.Utils.is_i16b_array 3328 ${result}"#)
    }

    pub(crate) fn ntt_multiply_pre(
        lhs: &[i16; 16],
        rhs: &[i16; 16],
        out: &[i16; 16],
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#" Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
                Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
                Spec.Utils.is_i16b_array 3328 ${lhs} /\
                Spec.Utils.is_i16b_array 3328 ${rhs} "#
        )
    }

    pub(crate) fn ntt_multiply_post(
        lhs: &[i16; 16],
        rhs: &[i16; 16],
        out: &[i16; 16],
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Spec.Utils.is_i16b_array 3328 ${result}"#)
    }

    pub(crate) fn serialize_1_pre(vec: &[i16; 16], out: &[u8]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"
            Seq.length ${out} == 2 /\ 
            Spec.MLKEM.serialize_pre 1 $vec"#
        )
    }

    pub(crate) fn serialize_1_post(vec: &[i16; 16], out: &[u8], result: &[u8]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"   
            Seq.length ${result} == 2 /\
            (Spec.MLKEM.serialize_pre 1 $vec ==> 
               Spec.MLKEM.serialize_post 1 ${vec} ${result})"#
        )
    }

    pub(crate) fn deserialize_1_pre(input: &[u8], out: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Seq.length ${input} == 2"#)
    }

    pub(crate) fn deserialize_1_post(
        input: &[u8],
        out: &[i16; 16],
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"
            Seq.length ${input} == 2 ==>
            Spec.MLKEM.deserialize_post 1 ${input} ${result}"#
        )
    }

    pub(crate) fn serialize_4_pre(vec: &[i16; 16], out: &[u8]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"
            Seq.length ${out} == 8 /\ 
            Spec.MLKEM.serialize_pre 4 $vec"#
        )
    }

    pub(crate) fn serialize_4_post(vec: &[i16; 16], out: &[u8], result: &[u8]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"   
            Seq.length ${result} == 8 /\
            (Spec.MLKEM.serialize_pre 4 $vec ==> 
               Spec.MLKEM.serialize_post 4 ${vec} ${result})"#
        )
    }

    pub(crate) fn deserialize_4_pre(input: &[u8], out: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Seq.length ${input} == 8"#)
    }

    pub(crate) fn deserialize_4_post(
        input: &[u8],
        out: &[i16; 16],
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"
            Seq.length ${input} == 8 ==>
            Spec.MLKEM.deserialize_post 4 ${input} ${result}"#
        )
    }

    pub(crate) fn serialize_10_pre(vec: &[i16; 16], out: &[u8]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"
            Seq.length ${out} == 20 /\ 
            Spec.MLKEM.serialize_pre 10 $vec"#
        )
    }

    pub(crate) fn serialize_10_post(vec: &[i16; 16], out: &[u8], result: &[u8]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"   
            Seq.length ${result} == 20 /\
            (Spec.MLKEM.serialize_pre 10 $vec ==> 
               Spec.MLKEM.serialize_post 10 ${vec} ${result})"#
        )
    }

    pub(crate) fn deserialize_10_pre(input: &[u8], out: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Seq.length ${input} == 20"#)
    }

    pub(crate) fn deserialize_10_post(
        input: &[u8],
        out: &[i16; 16],
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"
            Seq.length ${input} == 20 ==>
            Spec.MLKEM.deserialize_post 10 ${input} ${result}"#
        )
    }

    pub(crate) fn serialize_12_pre(vec: &[i16; 16], out: &[u8]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"
            Seq.length ${out} == 24 /\ 
            Spec.MLKEM.serialize_pre 12 $vec"#
        )
    }

    pub(crate) fn serialize_12_post(vec: &[i16; 16], out: &[u8], result: &[u8]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"   
            Seq.length ${result} == 24 /\
            (Spec.MLKEM.serialize_pre 12 $vec ==> 
               Spec.MLKEM.serialize_post 12 ${vec} ${result})"#
        )
    }

    pub(crate) fn deserialize_12_pre(input: &[u8], out: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Seq.length ${input} == 24"#)
    }

    pub(crate) fn deserialize_12_post(
        input: &[u8],
        out: &[i16; 16],
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"
            Seq.length ${input} == 24 ==>
            Spec.MLKEM.deserialize_post 12 ${input} ${result}"#
        )
    }
}

#[hax_lib::attributes]
pub trait Operations: Copy + Clone + Repr {
    #[requires(true)]
    #[allow(non_snake_case)]
    fn ZERO() -> Self;

    #[requires(array.len() == 16)]
    fn from_i16_array(array: &[I16], out: &mut Self);

    #[requires(array.len() == 16)]
    fn reducing_from_i32_array(array: &[I32], out: &mut Self);

    #[requires(out.len() == 16)]
    fn to_i16_array(x: &Self, out: &mut [i16]);

    #[requires(array.len() >= 32)]
    fn from_bytes(array: &[u8], out: &mut Self);

    #[requires(bytes.len() >= 32)]
    #[ensures(|_| future(bytes).len() == bytes.len())]
    fn to_bytes(x: Self, bytes: &mut [u8]);

    // Basic arithmetic
    // #[requires(spec::add_pre(&lhs.repr(), &rhs.repr()))]
    // #[ensures(|_| spec::add_post(&lhs.repr(), &rhs.repr(), &future(lhs).repr()))]
    #[requires(true)]
    fn add(lhs: &mut Self, rhs: &Self);

    // #[requires(spec::sub_pre(&lhs.repr(), &rhs.repr()))]
    // #[ensures(|_| spec::sub_post(&lhs.repr(), &rhs.repr(), &future(lhs).repr()))]
    #[requires(true)]
    fn sub(lhs: &mut Self, rhs: &Self);

    // #[requires(spec::negate_pre(&vec.repr()))]
    // #[ensures(|_| spec::negate_post(&vec.repr(), &future(vec).repr()))]
    #[requires(true)]
    fn negate(vec: &mut Self);

    // #[requires(spec::multiply_by_constant_pre(&vec.repr(), c))]
    // #[ensures(|_| spec::multiply_by_constant_post(&vec.repr(), c, &future(vec).repr()))]
    #[requires(true)]
    fn multiply_by_constant(vec: &mut Self, c: i16);

    // Bitwise operations
    // #[requires(true)]
    // #[ensures(|_| spec::bitwise_and_with_constant_constant_post(&vec.repr(), c, &future(vec).repr()))]
    #[requires(true)]
    fn bitwise_and_with_constant(vec: &mut Self, c: i16);

    #[requires(SHIFT_BY >= 0 && SHIFT_BY < 16)]
    // #[ensures(|_| spec::shift_right_post(&vec.repr(), SHIFT_BY, &future(vec).repr()))]
    fn shift_right<const SHIFT_BY: i32>(vec: &mut Self);

    // Modular operations
    // #[requires(spec::cond_subtract_3329_pre(&vec.repr()))]
    // #[ensures(|_| spec::cond_subtract_3329_post(&vec.repr(), &future(vec).repr()))]
    #[requires(true)]
    fn cond_subtract_3329(vec: &mut Self);

    // #[requires(spec::barrett_reduce_pre(&vec.repr()))]
    // #[ensures(|_| spec::barrett_reduce_post(&vec.repr(), &future(vec).repr()))]
    #[requires(true)]
    fn barrett_reduce(vec: &mut Self);

    // #[requires(spec::montgomery_multiply_by_constant_pre(&vec.repr(), c))]
    // #[ensures(|_| spec::montgomery_multiply_by_constant_post(&vec.repr(), c, &future(vec).repr()))]
    #[requires(true)]
    fn montgomery_multiply_by_constant(vec: &mut Self, c: i16);

    // Compression
    // #[requires(spec::compress_1_pre(&vec.repr()))]
    // #[ensures(|_| spec::compress_1_post(&vec.repr(), &future(vec).repr()))]
    #[requires(true)]
    fn compress_1(vec: &mut Self);

    // #[requires(spec::compress_pre(&vec.repr(), COEFFICIENT_BITS))]
    // #[ensures(|_| spec::compress_post(&vec.repr(), COEFFICIENT_BITS, &future(vec).repr()))]
    #[requires(COEFFICIENT_BITS >= 0 && COEFFICIENT_BITS <= 16)]
    fn compress<const COEFFICIENT_BITS: i32>(vec: &mut Self);

    // #[requires(spec::decompress_ciphertext_coefficient_pre(&vec.repr(), COEFFICIENT_BITS))]
    #[requires(0 <= COEFFICIENT_BITS && COEFFICIENT_BITS < 31)]
    fn decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(vec: &mut Self);

    // NTT
    #[requires(true)]
    fn ntt_layer_1_step(a: &mut Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16);
    #[requires(true)]
    fn ntt_layer_2_step(a: &mut Self, zeta0: i16, zeta1: i16);
    #[requires(true)]
    fn ntt_layer_3_step(a: &mut Self, zeta: i16);

    #[requires(true)]
    fn inv_ntt_layer_1_step(a: &mut Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16);
    #[requires(true)]
    fn inv_ntt_layer_2_step(a: &mut Self, zeta0: i16, zeta1: i16);
    #[requires(true)]
    fn inv_ntt_layer_3_step(a: &mut Self, zeta: i16);

    #[requires(out.len() >= 16)]
    #[ensures(|_| future(out).len() == out.len())]
    fn accumulating_ntt_multiply(
        lhs: &Self,
        rhs: &Self,
        out: &mut [I32],
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
    );

    #[requires(out.len() >= 16)]
    #[ensures(|_| future(out).len() == out.len())]
    fn accumulating_ntt_multiply_fill_cache(
        lhs: &Self,
        rhs: &Self,
        out: &mut [I32],
        cache: &mut Self,
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
    );

    #[requires(out.len() >= 16)]
    #[ensures(|_| future(out).len() == out.len())]
    fn accumulating_ntt_multiply_use_cache(lhs: &Self, rhs: &Self, out: &mut [I32], cache: &Self);

    // Serialization and deserialization
    #[requires(out.len() == 2)]
    #[ensures(|_| future(out).len() == 2)]
    fn serialize_1(a: &Self, out: &mut [U8]);
    #[requires(a.len() == 2)]
    fn deserialize_1(a: &[U8], out: &mut Self);

    #[requires(out.len() == 8)]
    #[ensures(|_| future(out).len() == 8)]
    fn serialize_4(a: &Self, out: &mut [u8]);
    #[requires(a.len() == 8)]
    fn deserialize_4(a: &[u8], out: &mut Self);

    #[requires(out.len() == 10)]
    #[ensures(|_| future(out).len() == 10)]
    fn serialize_5(a: &Self, out: &mut [u8]);
    #[requires(a.len() == 10)]
    fn deserialize_5(a: &[u8], out: &mut Self);

    #[requires(out.len() == 20)]
    #[ensures(|_| future(out).len() == 20)]
    fn serialize_10(a: &Self, out: &mut [u8]);
    #[requires(a.len() == 20)]
    fn deserialize_10(a: &[u8], out: &mut Self);

    #[requires(out.len() == 22)]
    #[ensures(|_| future(out).len() == 22)]
    fn serialize_11(a: &Self, out: &mut [u8]);
    #[requires(a.len() == 22)]
    fn deserialize_11(a: &[u8], out: &mut Self);

    #[requires(out.len() == 24)]
    #[ensures(|_| future(out).len() == 24)]
    fn serialize_12(a: &Self, out: &mut [U8]);
    #[requires(a.len() == 24)]
    fn deserialize_12(a: &[U8], out: &mut Self);

    #[requires(a.len() == 24 && out.len() == 16)]
    #[ensures(|result| result <= 16 && future(out).len() == 16)]
    fn rej_sample(a: &[u8], out: &mut [i16]) -> usize;
}

// hax does not support trait with default implementations, so we use the following pattern
#[inline(always)]
pub fn montgomery_multiply_fe<T: Operations>(v: &mut T, fer: i16) {
    T::montgomery_multiply_by_constant(v, fer)
}

#[inline(always)]
pub fn to_standard_domain<T: Operations>(v: &mut T) {
    T::montgomery_multiply_by_constant(v, MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS as i16)
}

#[inline(always)]
pub fn to_unsigned_representative<T: Operations>(a: &T, out: &mut T) {
    *out = *a; // XXX: We need a copy of `a` here. At least
               // the allocation becomes apparent on the
               // outside.
    T::shift_right::<15>(out);
    T::bitwise_and_with_constant(out, FIELD_MODULUS);
    T::add(out, a)
}

#[inline(always)]
pub fn decompress_1<T: Operations>(vec: &mut T) {
    T::negate(vec);
    T::bitwise_and_with_constant(vec, 1665);
}
