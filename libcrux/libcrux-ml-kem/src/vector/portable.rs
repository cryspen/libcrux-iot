use super::Operations;
use crate::polynomial::PolynomialRingElement;
use crate::polynomial::VECTORS_IN_RING_ELEMENT;
pub mod arithmetic;
mod compress;
pub mod ntt;
mod sampling;
mod serialize;
pub mod vector_type;

use arithmetic::*;
use compress::*;
use ntt::*;
use sampling::*;
use vector_type::*;

pub(crate) use vector_type::PortableVector;

impl crate::vector::traits::Repr for PortableVector {
    fn repr(x: Self) -> [i16; 16] {
        to_i16_array(x)
    }
}

#[hax_lib::requires(fstar!(r#"Spec.MLKEM.serialize_pre 1 (impl.f_repr $a)"#))]
#[hax_lib::ensures(|out| fstar!(r#"Spec.MLKEM.serialize_pre 1 (impl.f_repr $a) ==> 
                                 Spec.MLKEM.serialize_post 1 (impl.f_repr $a) $out"#))]
fn serialize_1(a: PortableVector) -> [u8; 2] {
    hax_lib::fstar!(
        r#"assert (forall i. Rust_primitives.bounded (Seq.index ${a}.f_elements i) 1)"#
    );
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.serialize_1_lemma $a"#);
    match a {
        PortableVector::Unpacked { elements } => serialize::serialize_1(elements),
        _ => panic!(),
    }
}

#[hax_lib::requires(a.len() == 2)]
#[hax_lib::ensures(|out| fstar!(r#"sz (Seq.length $a) =. sz 2 ==> Spec.MLKEM.deserialize_post 1 $a (impl.f_repr $out)"#))]
fn deserialize_1(a: &[u8]) -> PortableVector {
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_1_lemma $a"#);
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_1_bounded_lemma $a"#);
    PortableVector::Unpacked {
        elements: serialize::deserialize_1(a),
    }
}

#[hax_lib::requires(fstar!(r#"Spec.MLKEM.serialize_pre 4 (impl.f_repr $a)"#))]
#[hax_lib::ensures(|out| fstar!(r#"Spec.MLKEM.serialize_pre 4 (impl.f_repr $a) ==> Spec.MLKEM.serialize_post 4 (impl.f_repr $a) $out"#))]
fn serialize_4(a: PortableVector) -> [u8; 8] {
    hax_lib::fstar!(
        r#"assert (forall i. Rust_primitives.bounded (Seq.index ${a}.f_elements i) 4)"#
    );
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.serialize_4_lemma $a"#);
    match a {
        PortableVector::Unpacked { elements } => serialize::serialize_4(elements),
        _ => panic!(),
    }
}

#[hax_lib::requires(a.len() == 8)]
#[hax_lib::ensures(|out| fstar!(r#"sz (Seq.length $a) =. sz 8 ==> Spec.MLKEM.deserialize_post 4 $a (impl.f_repr $out)"#))]
fn deserialize_4(a: &[u8]) -> PortableVector {
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_4_lemma $a"#);
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_4_bounded_lemma $a"#);
    PortableVector::Unpacked {
        elements: serialize::deserialize_4(a),
    }
}

fn serialize_5(a: PortableVector) -> [u8; 10] {
    match a {
        PortableVector::Unpacked { elements } => serialize::serialize_5(elements),
        _ => panic!(),
    }
}

#[hax_lib::requires(a.len() == 10)]
fn deserialize_5(a: &[u8]) -> PortableVector {
    PortableVector::Unpacked {
        elements: serialize::deserialize_5(a),
    }
}

#[hax_lib::requires(fstar!(r#"Spec.MLKEM.serialize_pre 10 (impl.f_repr $a)"#))]
#[hax_lib::ensures(|out| fstar!(r#"Spec.MLKEM.serialize_pre 10 (impl.f_repr $a) ==> Spec.MLKEM.serialize_post 10 (impl.f_repr $a) $out"#))]
fn serialize_10(a: PortableVector) -> [u8; 20] {
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.serialize_10_lemma $a"#);
    match a {
        PortableVector::Unpacked { elements } => serialize::serialize_10(elements),
        _ => panic!(),
    }
}

#[hax_lib::requires(a.len() == 20)]
#[hax_lib::ensures(|out| fstar!(r#"sz (Seq.length $a) =. sz 20 ==> Spec.MLKEM.deserialize_post 10 $a (impl.f_repr $out)"#))]
fn deserialize_10(a: &[u8]) -> PortableVector {
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_10_lemma $a"#);
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_10_bounded_lemma $a"#);
    PortableVector::Unpacked {
        elements: serialize::deserialize_10(a),
    }
}

fn serialize_11(a: PortableVector) -> [u8; 22] {
    match a {
        PortableVector::Unpacked { elements } => serialize::serialize_11(elements),
        _ => panic!(),
    }
}

#[hax_lib::requires(a.len() == 22)]
fn deserialize_11(a: &[u8]) -> PortableVector {
    PortableVector::Unpacked {
        elements: serialize::deserialize_11(a),
    }
}

#[hax_lib::requires(fstar!(r#"Spec.MLKEM.serialize_pre 12 (impl.f_repr $a)"#))]
#[hax_lib::ensures(|out| fstar!(r#"Spec.MLKEM.serialize_pre 12 (impl.f_repr $a) ==> Spec.MLKEM.serialize_post 12 (impl.f_repr $a) $out"#))]
fn serialize_12(a: PortableVector) -> [u8; 24] {
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.serialize_12_lemma $a"#);
    match a {
        PortableVector::Unpacked { elements } => serialize::serialize_12(elements),
        _ => panic!(),
    }
}

#[hax_lib::requires(a.len() == 24)]
#[hax_lib::ensures(|out| fstar!(r#"sz (Seq.length $a) =. sz 24 ==> Spec.MLKEM.deserialize_post 12 $a (impl.f_repr $out)"#))]
fn deserialize_12(a: &[u8]) -> PortableVector {
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_12_lemma $a"#);
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_12_bounded_lemma $a"#);
    PortableVector::Unpacked {
        elements: serialize::deserialize_12(a),
    }
}

#[hax_lib::fstar::before(r#"#push-options "--z3rlimit 400 --split_queries always""#)]
#[hax_lib::fstar::after(r#"#pop-options"#)]
#[hax_lib::attributes]
impl Operations for PortableVector {
    fn ntt_binomially_sampled(zeta: &mut usize, vectors: &mut [Self; VECTORS_IN_RING_ELEMENT])
    {
        ntt_binomially_sampled(zeta, vectors)
    }
    
    
    #[inline(always)]
    fn ntt(zeta: &mut usize, vectors: &mut [Self; VECTORS_IN_RING_ELEMENT]) {
        ntt(zeta, vectors)
    }

    #[ensures(|out| fstar!(r#"impl.f_repr out == Seq.create 16 0s"#))]
    fn ZERO() -> Self {
        zero()
    }

    #[requires(array.len() == 16)]
    #[ensures(|out| fstar!(r#"impl.f_repr out == $array"#))]
    fn from_i16_array(array: &[i16]) -> Self {
        from_i16_array(array)
    }

    #[ensures(|out| fstar!(r#"out == impl.f_repr $x"#))]
    fn to_i16_array(x: Self) -> [i16; 16] {
        to_i16_array(x)
    }

    #[requires(fstar!(r#"forall i. i < 16 ==> 
        Spec.Utils.is_intb (pow2 15 - 1) (v (Seq.index ${lhs}.f_elements i) + v (Seq.index ${rhs}.f_elements i))"#))]
    #[ensures(|result| fstar!(r#"forall i. i < 16 ==> 
        (v (Seq.index ${result}.f_elements i) == 
         v (Seq.index ${lhs}.f_elements i) + v (Seq.index ${rhs}.f_elements i))"#))]
    fn add(lhs: Self, rhs: &Self) -> Self {
        match (lhs, rhs) {
            (
                PortableVector::Unpacked {
                    elements: elements_a,
                },
                PortableVector::Unpacked {
                    elements: elements_b,
                },
            ) => PortableVector::Unpacked {
                elements: add(elements_a, elements_b),
            },
            _ => panic!(),
        }
    }

    #[requires(fstar!(r#"forall i. i < 16 ==> 
        Spec.Utils.is_intb (pow2 15 - 1) (v (Seq.index ${lhs}.f_elements i) - v (Seq.index ${rhs}.f_elements i))"#))]
    #[ensures(|result| fstar!(r#"forall i. i < 16 ==> 
        (v (Seq.index ${result}.f_elements i) == 
         v (Seq.index ${lhs}.f_elements i) - v (Seq.index ${rhs}.f_elements i))"#))]
    fn sub(lhs: Self, rhs: &Self) -> Self {
        match (lhs, rhs) {
            (
                PortableVector::Unpacked {
                    elements: elements_a,
                },
                PortableVector::Unpacked {
                    elements: elements_b,
                },
            ) => PortableVector::Unpacked {
                elements: sub(elements_a, elements_b),
            },
            _ => panic!(),
        }
    }

    #[requires(fstar!(r#"forall i. i < 16 ==> 
        Spec.Utils.is_intb (pow2 15 - 1) (v (Seq.index ${vec}.f_elements i) * v c)"#))]
    #[ensures(|result| fstar!(r#"forall i. i < 16 ==> 
        (v (Seq.index ${result}.f_elements i) == 
        v (Seq.index ${vec}.f_elements i) * v c)"#))]
    fn multiply_by_constant(vec: Self, c: i16) -> Self {
        match vec {
            PortableVector::Unpacked { elements } => PortableVector::Unpacked {
                elements: multiply_by_constant(elements, c),
            },
            _ => panic!(),
        }
    }

    #[ensures(|out| fstar!(r#"impl.f_repr out == Spec.Utils.map_array (fun x -> x &. c) (impl.f_repr $v)"#))]
    fn bitwise_and_with_constant(v: Self, c: i16) -> Self {
        match v {
            PortableVector::Unpacked { elements } => PortableVector::Unpacked {
                elements: bitwise_and_with_constant(elements, c),
            },
            _ => panic!(),
        }
    }

    #[requires(SHIFT_BY >= 0 && SHIFT_BY < 16)]
    #[ensures(|out| fstar!(r#"(v_SHIFT_BY >=. 0l /\ v_SHIFT_BY <. 16l) ==> impl.f_repr out == Spec.Utils.map_array (fun x -> x >>! ${SHIFT_BY}) (impl.f_repr $v)"#))]
    fn shift_right<const SHIFT_BY: i32>(v: Self) -> Self {
        match v {
            PortableVector::Unpacked { elements } => PortableVector::Unpacked {
                elements: shift_right::<{ SHIFT_BY }>(elements),
            },
            _ => panic!(),
        }
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b_array (pow2 12 - 1) (impl.f_repr $v)"#))]
    #[ensures(|out| fstar!(r#"impl.f_repr out == Spec.Utils.map_array (fun x -> if x >=. 3329s then x -! 3329s else x) (impl.f_repr $v)"#))]
    fn cond_subtract_3329(v: Self) -> Self {
        match v {
            PortableVector::Unpacked { elements } => PortableVector::Unpacked {
                elements: cond_subtract_3329(elements),
            },
            _ => panic!(),
        }
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b_array 28296 (impl.f_repr ${v})"#))]
    fn barrett_reduce(v: Self) -> Self {
        match v {
            PortableVector::Unpacked { elements } => PortableVector::Unpacked {
                elements: barrett_reduce(elements),
            },
            _ => panic!(),
        }
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 $r"#))]
    fn montgomery_multiply_by_constant(v: Self, r: i16) -> Self {
        match v {
            PortableVector::Unpacked { elements } => PortableVector::Unpacked {
                elements: montgomery_multiply_by_constant(elements, r),
            },
            _ => panic!(),
        }
    }

    #[requires(fstar!(r#"forall (i:nat). i < 16 ==> v (Seq.index (impl.f_repr $a) i) >= 0 /\
        v (Seq.index (impl.f_repr $a) i) < 3329"#))]
    #[ensures(|out| fstar!(r#"forall (i:nat). i < 16 ==> bounded (Seq.index (impl.f_repr $out) i) 1"#))]
    fn compress_1(a: Self) -> Self {
        match a {
            PortableVector::Unpacked { elements } => PortableVector::Unpacked {
                elements: compress_1(elements),
            },
            _ => panic!(),
        }
    }

    #[requires(fstar!(r#"(v $COEFFICIENT_BITS == 4 \/
            v $COEFFICIENT_BITS == 5 \/
            v $COEFFICIENT_BITS == 10 \/
            v $COEFFICIENT_BITS == 11) /\
        (forall (i:nat). i < 16 ==> v (Seq.index (impl.f_repr $a) i) >= 0 /\
            v (Seq.index (impl.f_repr $a) i) < 3329)"#))]
    #[ensures(|out| fstar!(r#"(v $COEFFICIENT_BITS == 4 \/
            v $COEFFICIENT_BITS == 5 \/
            v $COEFFICIENT_BITS == 10 \/
            v $COEFFICIENT_BITS == 11) ==>
                (forall (i:nat). i < 16 ==> bounded (Seq.index (impl.f_repr $out) i) (v $COEFFICIENT_BITS))"#))]
    fn compress<const COEFFICIENT_BITS: i32>(a: Self) -> Self {
        match a {
            PortableVector::Unpacked { elements } => PortableVector::Unpacked {
                elements: compress::<COEFFICIENT_BITS>(elements),
            },
            _ => panic!(),
        }
    }

    #[requires(fstar!(r#"(v $COEFFICIENT_BITS == 4 \/
        v $COEFFICIENT_BITS == 5 \/
        v $COEFFICIENT_BITS == 10 \/
        v $COEFFICIENT_BITS == 11) /\
    (forall (i:nat). i < 16 ==> v (Seq.index (impl.f_repr $a) i) >= 0 /\
        v (Seq.index (impl.f_repr $a) i) < pow2 (v $COEFFICIENT_BITS))"#))]
    fn decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(a: Self) -> Self {
        match a {
            PortableVector::Unpacked { elements } => PortableVector::Unpacked {
                elements: decompress_ciphertext_coefficient::<COEFFICIENT_BITS>(elements),
            },
            _ => panic!(),
        }
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\ 
                       Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3  /\
                       Spec.Utils.is_i16b_array (11207+5*3328) (impl.f_repr ${a})"#))]
    #[ensures(|out| fstar!(r#"Spec.Utils.is_i16b_array (11207+6*3328) (impl.f_repr $out)"#))]
    fn ntt_layer_1_step(a: Self, zeta0: usize, zeta1: usize, zeta2: usize, zeta3: usize) -> Self {
        match a {
            PortableVector::Unpacked { elements } => PortableVector::Unpacked {
                elements: ntt_layer_1_step_unpacked(elements, zeta0, zeta1, zeta2, zeta3),
            },
            #[cfg(feature = "armv7em")]
            PortableVector::Packed { elements } => PortableVector::Packed {
                elements: ntt_layer_1_step_packed(elements, zeta0, zeta1, zeta2, zeta3),
            },
            _ => panic!(),
        }
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
                       Spec.Utils.is_i16b_array (11207+4*3328) (impl.f_repr ${a})"#))]
    #[ensures(|out| fstar!(r#"Spec.Utils.is_i16b_array (11207+5*3328) (impl.f_repr $out)"#))]
    fn ntt_layer_2_step(a: Self, zeta0: usize, zeta1: usize) -> Self {
        match a {
            PortableVector::Unpacked { elements } => PortableVector::Unpacked {
                elements: ntt_layer_2_step_unpacked(elements, zeta0, zeta1),
            },
            #[cfg(feature = "armv7em")]
            PortableVector::Packed { elements } => PortableVector::Packed {
                elements: ntt_layer_2_step_packed(elements, zeta0, zeta1),
            },
            #[cfg(not(feature = "armv7em"))]
            _ => panic!(),
        }
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta /\
                       Spec.Utils.is_i16b_array (11207+3*3328) (impl.f_repr ${a})"#))]
    #[ensures(|out| fstar!(r#"Spec.Utils.is_i16b_array (11207+4*3328) (impl.f_repr $out)"#))]
    fn ntt_layer_3_step(a: Self, zeta: usize) -> Self {
        match a {
            PortableVector::Unpacked { elements } => PortableVector::Unpacked {
                elements: ntt_layer_3_step_unpacked(elements, zeta),
            },
            // If on Cortex-M4, this is where we pack the vector.
            #[cfg(feature = "armv7em")]
            PortableVector::Packed { elements } => PortableVector::Packed {
                elements: ntt_layer_3_step_packed(elements, zeta),
            },
            _ => panic!(),
        }
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\ 
                       Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
                       Spec.Utils.is_i16b_array (4*3328) (impl.f_repr ${a})"#))]
    #[ensures(|out| fstar!(r#"Spec.Utils.is_i16b_array 3328 (impl.f_repr $out)"#))]
    fn inv_ntt_layer_1_step(a: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self {
        match a {
            PortableVector::Unpacked { elements } => PortableVector::Unpacked {
                elements: inv_ntt_layer_1_step(elements, zeta0, zeta1, zeta2, zeta3),
            },
            _ => panic!(),
        }
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
                       Spec.Utils.is_i16b_array 3328 (impl.f_repr ${a})"#))]
    #[ensures(|out| fstar!(r#"Spec.Utils.is_i16b_array 3328 (impl.f_repr $out)"#))]
    fn inv_ntt_layer_2_step(a: Self, zeta0: i16, zeta1: i16) -> Self {
        match a {
            PortableVector::Unpacked { elements } => PortableVector::Unpacked {
                elements: inv_ntt_layer_2_step(elements, zeta0, zeta1),
            },
            _ => panic!(),
        }
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta /\
                       Spec.Utils.is_i16b_array 3328 (impl.f_repr ${a})"#))]
    #[ensures(|out| fstar!(r#"Spec.Utils.is_i16b_array 3328 (impl.f_repr $out)"#))]
    fn inv_ntt_layer_3_step(a: Self, zeta: i16) -> Self {
        match a {
            PortableVector::Unpacked { elements } => PortableVector::Unpacked {
                elements: inv_ntt_layer_3_step(elements, zeta),
            },
            _ => panic!(),
        }
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
                       Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
                       Spec.Utils.is_i16b_array 3328 (impl.f_repr ${lhs}) /\
                       Spec.Utils.is_i16b_array 3328 (impl.f_repr ${rhs})"#))]
    #[ensures(|out| fstar!(r#"Spec.Utils.is_i16b_array 3328 (impl.f_repr $out)"#))]
    fn ntt_multiply(
        lhs: &Self,
        rhs: &Self,
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
    ) -> Self {
        match (lhs, rhs) {
            (
                PortableVector::Unpacked {
                    elements: elements_a,
                },
                PortableVector::Unpacked {
                    elements: elements_b,
                },
            ) => PortableVector::Unpacked {
                elements: ntt_multiply(elements_a, elements_b, zeta0, zeta1, zeta2, zeta3),
            },
            _ => panic!(),
        }
    }

    #[requires(fstar!(r#"Spec.MLKEM.serialize_pre 1 (impl.f_repr $a)"#))]
    #[ensures(|out| fstar!(r#"Spec.MLKEM.serialize_pre 1 (impl.f_repr $a) ==> Spec.MLKEM.serialize_post 1 (impl.f_repr $a) $out"#))]
    fn serialize_1(a: Self) -> [u8; 2] {
        serialize_1(a)
    }

    #[requires(a.len() == 2)]
    #[ensures(|out| fstar!(r#"sz (Seq.length $a) =. sz 2 ==> Spec.MLKEM.deserialize_post 1 $a (impl.f_repr $out)"#))]
    fn deserialize_1(a: &[u8]) -> Self {
        deserialize_1(a)
    }

    #[requires(fstar!(r#"Spec.MLKEM.serialize_pre 4 (impl.f_repr $a)"#))]
    #[ensures(|out| fstar!(r#"Spec.MLKEM.serialize_pre 4 (impl.f_repr $a) ==> Spec.MLKEM.serialize_post 4 (impl.f_repr $a) $out"#))]
    fn serialize_4(a: Self) -> [u8; 8] {
        serialize_4(a)
    }

    #[requires(a.len() == 8)]
    #[ensures(|out| fstar!(r#"sz (Seq.length $a) =. sz 8 ==> Spec.MLKEM.deserialize_post 4 $a (impl.f_repr $out)"#))]
    fn deserialize_4(a: &[u8]) -> Self {
        deserialize_4(a)
    }

    fn serialize_5(a: Self) -> [u8; 10] {
        serialize_5(a)
    }

    #[requires(a.len() == 10)]
    fn deserialize_5(a: &[u8]) -> Self {
        deserialize_5(a)
    }

    #[requires(fstar!(r#"Spec.MLKEM.serialize_pre 10 (impl.f_repr $a)"#))]
    #[ensures(|out| fstar!(r#"Spec.MLKEM.serialize_pre 10 (impl.f_repr $a) ==> Spec.MLKEM.serialize_post 10 (impl.f_repr $a) $out"#))]
    fn serialize_10(a: Self) -> [u8; 20] {
        serialize_10(a)
    }

    #[requires(a.len() == 20)]
    #[ensures(|out| fstar!(r#"sz (Seq.length $a) =. sz 20 ==> Spec.MLKEM.deserialize_post 10 $a (impl.f_repr $out)"#))]
    fn deserialize_10(a: &[u8]) -> Self {
        deserialize_10(a)
    }

    fn serialize_11(a: Self) -> [u8; 22] {
        serialize_11(a)
    }

    #[requires(a.len() == 22)]
    fn deserialize_11(a: &[u8]) -> Self {
        deserialize_11(a)
    }

    #[requires(fstar!(r#"Spec.MLKEM.serialize_pre 12 (impl.f_repr $a)"#))]
    #[ensures(|out| fstar!(r#"Spec.MLKEM.serialize_pre 12 (impl.f_repr $a) ==> Spec.MLKEM.serialize_post 12 (impl.f_repr $a) $out"#))]
    fn serialize_12(a: Self) -> [u8; 24] {
        serialize_12(a)
    }

    #[requires(a.len() == 24)]
    #[ensures(|out| fstar!(r#"sz (Seq.length $a) =. sz 24 ==> Spec.MLKEM.deserialize_post 12 $a (impl.f_repr $out)"#))]
    fn deserialize_12(a: &[u8]) -> Self {
        deserialize_12(a)
    }

    #[requires(a.len() == 24 && out.len() == 16)]
    #[ensures(|result|
        fstar!(r#"Seq.length $out_future == Seq.length $out /\ v $result <= 16"#)
    )]
    fn rej_sample(a: &[u8], out: &mut [i16]) -> usize {
        rej_sample(a, out)
    }
}
