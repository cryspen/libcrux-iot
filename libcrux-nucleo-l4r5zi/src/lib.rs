#![no_main]
#![no_std]

use cortex_m_semihosting::debug;

use defmt_rtt as _; // global logger

use embassy_stm32 as _; // memory layout

use panic_probe as _;

pub const COREFREQ: u32 = 4_000_000;

// same panicking *behavior* as `panic-probe` but doesn't print a panic message
// this prevents the panic message being printed *twice* when `defmt::panic` is invoked
#[defmt::panic_handler]
fn panic() -> ! {
    cortex_m::asm::udf()
}

/// Terminates the application and makes a semihosting-capable debug tool exit
/// with status code 0.
pub fn exit() -> ! {
    loop {
        debug::exit(debug::EXIT_SUCCESS);
    }
}

/// Hardfault handler.
///
/// Terminates the application and makes a semihosting-capable debug tool exit
/// with an error. This seems better than the default, which is to spin in a
/// loop.
#[cortex_m_rt::exception]
unsafe fn HardFault(_frame: &cortex_m_rt::ExceptionFrame) -> ! {
    loop {
        debug::exit(debug::EXIT_FAILURE);
    }
}

fn pack(a: i16, b: i16) -> u32 {
    ((a as u32) << 16) | (b as u32 & 0xffff)
}

fn unpack(val: u32) -> (i16, i16) {
    ((val / (1 << 16)) as i16, (val & 0xffff) as i16)
}

// defmt-test 0.3.0 has the limitation that this `#[tests]` attribute can only be used
// once within a crate. the module can be in any file but there can only be at most
// one `#[tests]` module in this library crate
#[cfg(test)]
#[defmt_test::tests]
mod unit_tests {
    use super::*;
    use defmt::assert;
    use libcrux_ml_kem::{
        cortex_m::{
            arithmetic::{ntt_layer_1_step, plantard_double_ct, plantard_double_ct_reference},
            vector::PackedVector,
        },
        vector::portable::vector_type::PortableVector,
    };

    #[test]
    fn pack_unpack() {
        let a: i16 = 12;
        let b: i16 = -32767;

        let packed = pack(a,b);
        defmt::println!("packed_a,b: {=u32:#06x}", packed);
        assert_eq!(unpack(packed), (a,b));

        let packed = pack(b,a);
        defmt::println!("packed_b,a: {=u32:#06x}", packed);
        assert_eq!(unpack(packed), (b,a));
        
    }

    #[test]
    fn single_butterfly() {
        // a random test vector
        // let test_vec = [-29819, 23791, -27859, 26502, -5543, 20338, -25093, -2930, 6760, -12883, -7650, -15882, -14386, -11355, -22024, 19879];
        let test_vec = [
            20876, -20791, 27362, -15166, -31090, -28225, 21964, -21718, 10206, -20378, -14285,
            -9419, -9716, 27629, -28270, -10621,
        ];
        let portable = libcrux_ml_kem::vector::portable::vector_type::from_i16_array(&test_vec);
        let packed = PackedVector::from(portable);

        macro_rules! sliding_window {
            ($i:ident) => {
                let (a, b) =
                    plantard_double_ct(packed.elements[$i], packed.elements[$i + 1], 1290168);
                let (a_reference, b_reference) =
                    plantard_double_ct(packed.elements[$i], packed.elements[$i + 1], 1290168);
                assert_eq!(a, a_reference, "left-hand result, index {}", $i);
                assert_eq!(b, b_reference, "right-hand result, index {}", $i);
            };
        }

        for i in 0..=6 {
            sliding_window!(i);
        }
    }

    #[test]
    fn butterfly_spec() {
        let test_vec = [20876, -20791, 27362, -15166];
        let zeta1 = 1290168;
        let zeta2 = -2064267850;
        
        let a = pack(test_vec[0], test_vec[1]);
        let b = pack(test_vec[2], test_vec[3]);
        defmt::println!("packed");
        let (a, b) = plantard_double_ct_reference(a, b, zeta1);
        defmt::println!("butterfly packed");
        let results = [unpack(a).0, unpack(a).1, unpack(b).0, unpack(b).1];
        defmt::println!("butterfly unpacked ");
        let expected = [22007, -20997, 19745, -20585];

        for i in expected{
            defmt::println!("expected: {=i16}", i);
        }
        for i in results {
            defmt::println!("res:      {=i16}", i);
        }
    }
    // #[test]
    // fn layer_equality() {
    //     // a random test vector
    //     let test_vec = [
    //         20876, -20791, 27362, -15166, -31090, -28225, 21964, -21718, 10206, -20378, -14285,
    //         -9419, -9716, 27629, -28270, -10621,
    //     ];
    //     let portable = libcrux_ml_kem::vector::portable::vector_type::from_i16_array(&test_vec);
    //     let packed = PackedVector::from(portable);

    //     let zetas = [1290168, -2064267850, -966335387, -51606696];
    //     let res = ntt_layer_1_step(
    //         packed,
    //         zetas[0] as u32,
    //         zetas[1] as u32,
    //         zetas[2] as u32,
    //         zetas[3] as u32,
    //         plantard_double_ct,
    //     );
    //     let res_reference = ntt_layer_1_step(
    //         packed,
    //         zetas[0] as u32,
    //         zetas[1] as u32,
    //         zetas[2] as u32,
    //         zetas[3] as u32,
    //         plantard_double_ct_reference,
    //     );

    //     for i in 0..8 {
    //         assert_eq!(
    //             res.elements[i], res_reference.elements[i],
    //             "Difference in result at index: {}",
    //             i
    //         );
    //     }
    // }
}
