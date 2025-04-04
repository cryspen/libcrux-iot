//! This binary measures cycles for SHA-3 & SHAKE with input/output
//! lengths as required by ML-KEM.
//!
//! ⚠️ NOTE: Make sure to `#[inline(never)]` any function under test, to
//! get sensible results.

#![no_main]
#![no_std]

use board::cycle_counter::CycleCounter;
use board::init::setup_cycle_counter;

use core::ptr::{addr_of, addr_of_mut};

use rand_core::RngCore;

use libcrux_nucleo_l4r5zi::{self as board, init::ClockConfig}; // global logger + panicking-behavior + memory layout

// G aka SHA3-512
const G_DIGEST_SIZE: usize = 64;
const G_INPUT_SIZE_1: usize = 32; // CPA_PKE_KEY_GENERATION_SEED_SIZE
const G_INPUT_SIZE_2: usize = 2 * H_DIGEST_SIZE; // ind_cca::encapsulate,decapsulate

// H aka SHA3-256
const H_DIGEST_SIZE: usize = 32;
const H_INPUT_RANDOMNESS_SIZE: usize = 32; // SHARED_SECRET_SIZE

const H_INPUT_CIPHERTEXT_SIZE_512: usize = 768; // CIPHERTEXT_SIZE
const H_INPUT_CIPHERTEXT_SIZE_768: usize = 1088; // CIPHERTEXT_SIZE
const H_INPUT_CIPHERTEXT_SIZE_1024: usize = 1568; // CIPHERTEXT_SIZE
const H_INPUT_PUBLIC_KEY_SIZE_512: usize = 800; // PUBLIC_KEY_SIZE
const H_INPUT_PUBLIC_KEY_SIZE_768: usize = 1184; // PUBLIC_KEY_SIZE
const H_INPUT_PUBLIC_KEY_SIZE_1024: usize = 1568; // PUBLIC_KEY_SIZE

// For XOFs we pair occurring (input, output) sizes

// PRF aka SHAKE256
const PRF_KDF: (usize, usize) = (2 * H_DIGEST_SIZE, 32);
const PRF_IMPLICIT_REJECTION_SHARED_SECRET_512: (usize, usize) = (800, 32);
const PRF_IMPLICIT_REJECTION_SHARED_SECRET_768: (usize, usize) = (1120, 32);
const PRF_IMPLICIT_REJECTION_SHARED_SECRET_1024: (usize, usize) = (1600, 32);
const PRF_ETA2_RANDOMNESS_512: (usize, usize) = (33, 128);
const PRF_ETA2_RANDOMNESS_768: (usize, usize) = (33, 128);
const PRF_ETA2_RANDOMNESS_1024: (usize, usize) = (33, 128);
const PRF_ETA1_RANDOMNESS_512: (usize, usize) = (33, 192);
const PRF_ETA1_RANDOMNESS_768: (usize, usize) = (33, 128);
const PRF_ETA1_RANDOMNESS_1024: (usize, usize) = (33, 128);

// SHAKE128
const INIT_ABSORB_FINAL_INPUT_SIZE: usize = 34;
const BLOCK_SIZE: usize = 168;
const THREE_BLOCKS: usize = BLOCK_SIZE * 3;

#[cortex_m_rt::entry]
fn main() -> ! {
    // Set up the system clock.
    let clock_config = ClockConfig::CycleBenchmark;
    let p = board::init::setup_clock(clock_config);

    setup_cycle_counter();

    let mut rng = board::init::init_rng(p);

    // G aka SHA3-512
    let mut g_digest = [0u8; G_DIGEST_SIZE];

    {
        let mut g_input_1 = [0u8; G_INPUT_SIZE_1];
        rng.fill_bytes(&mut g_input_1);
        let start = CycleCounter::start_measurement();
        core::hint::black_box(libcrux_sha3::portable::sha512(&mut g_digest, &g_input_1));
        CycleCounter::end_measurement("libcrux SHA3-512 (G_INPUT_SIZE_1)", start);

        let start = CycleCounter::start_measurement();
        core::hint::black_box(unsafe {
            libcrux_pqm4::sha3_512(
                addr_of_mut!(g_digest[0]),
                addr_of!(g_input_1[0]),
                G_INPUT_SIZE_1,
            )
        });
        CycleCounter::end_measurement("PQM4 SHA3-512 (G_INPUT_SIZE_1)", start);
    }

    {
        let mut g_input_2 = [0u8; G_INPUT_SIZE_2];
        rng.fill_bytes(&mut g_input_2);
        let start = CycleCounter::start_measurement();
        core::hint::black_box(libcrux_sha3::portable::sha512(&mut g_digest, &g_input_2));
        CycleCounter::end_measurement("libcrux SHA3-512 (G_INPUT_SIZE_2)", start);

        let start = CycleCounter::start_measurement();
        core::hint::black_box(unsafe {
            libcrux_pqm4::sha3_512(
                addr_of_mut!(g_digest[0]),
                addr_of!(g_input_2[0]),
                G_INPUT_SIZE_2,
            )
        });
        CycleCounter::end_measurement("PQM4 SHA3-512 (G_INPUT_SIZE_1)", start);
    }

    // H aka SHA3-256
    let mut h_digest = [0u8; H_DIGEST_SIZE];
    {
        let mut h_input = [0u8; H_INPUT_RANDOMNESS_SIZE];
        rng.fill_bytes(&mut h_input);
        let start = CycleCounter::start_measurement();
        core::hint::black_box(libcrux_sha3::portable::sha256(&mut h_digest, &h_input));
        CycleCounter::end_measurement("libcrux SHA3-256 (H_INPUT_RANDOMNESS_SIZE)", start);

        let start = CycleCounter::start_measurement();
        core::hint::black_box(unsafe {
            libcrux_pqm4::sha3_256(
                addr_of_mut!(h_digest[0]),
                addr_of!(h_input[0]),
                H_INPUT_RANDOMNESS_SIZE,
            )
        });
        CycleCounter::end_measurement("PQM4 SHA3-256 (H_INPUT_RANDOMNESS_SIZE)", start);
    }
    {
        let mut h_input = [0u8; H_INPUT_CIPHERTEXT_SIZE_512];
        rng.fill_bytes(&mut h_input);
        let start = CycleCounter::start_measurement();
        core::hint::black_box(libcrux_sha3::portable::sha256(&mut h_digest, &h_input));
        CycleCounter::end_measurement("libcrux SHA3-256 (H_INPUT_CIPHERTEXT_SIZE_512)", start);

        let start = CycleCounter::start_measurement();
        core::hint::black_box(unsafe {
            libcrux_pqm4::sha3_256(
                addr_of_mut!(h_digest[0]),
                addr_of!(h_input[0]),
                H_INPUT_CIPHERTEXT_SIZE_512,
            )
        });
        CycleCounter::end_measurement("PQM4 SHA3-256 (H_INPUT_CIPHERTEXT_SIZE_512)", start);
    }
    {
        let mut h_input = [0u8; H_INPUT_CIPHERTEXT_SIZE_768];
        rng.fill_bytes(&mut h_input);
        let start = CycleCounter::start_measurement();
        core::hint::black_box(libcrux_sha3::portable::sha256(&mut h_digest, &h_input));
        CycleCounter::end_measurement("libcrux SHA3-256 (H_INPUT_CIPHERTEXT_SIZE_768)", start);

        let start = CycleCounter::start_measurement();
        core::hint::black_box(unsafe {
            libcrux_pqm4::sha3_256(
                addr_of_mut!(h_digest[0]),
                addr_of!(h_input[0]),
                H_INPUT_CIPHERTEXT_SIZE_768,
            )
        });
        CycleCounter::end_measurement("PQM4 SHA3-256 (H_INPUT_CIPHERTEXT_SIZE_768)", start);
    }
    {
        let mut h_input = [0u8; H_INPUT_CIPHERTEXT_SIZE_1024];
        rng.fill_bytes(&mut h_input);
        let start = CycleCounter::start_measurement();
        core::hint::black_box(libcrux_sha3::portable::sha256(&mut h_digest, &h_input));
        CycleCounter::end_measurement("libcrux SHA3-256 (H_INPUT_CIPHERTEXT_SIZE_1024)", start);

        let start = CycleCounter::start_measurement();
        core::hint::black_box(unsafe {
            libcrux_pqm4::sha3_256(
                addr_of_mut!(h_digest[0]),
                addr_of!(h_input[0]),
                H_INPUT_CIPHERTEXT_SIZE_1024,
            )
        });
        CycleCounter::end_measurement("PQM4 SHA3-256 (H_INPUT_CIPHERTEXT_SIZE_1024)", start);
    }

    {
        let mut h_input = [0u8; H_INPUT_PUBLIC_KEY_SIZE_512];
        rng.fill_bytes(&mut h_input);
        let start = CycleCounter::start_measurement();
        core::hint::black_box(libcrux_sha3::portable::sha256(&mut h_digest, &h_input));
        CycleCounter::end_measurement("libcrux SHA3-256 (H_INPUT_PUBLIC_KEY_SIZE_512)", start);

        let start = CycleCounter::start_measurement();
        core::hint::black_box(unsafe {
            libcrux_pqm4::sha3_256(
                addr_of_mut!(h_digest[0]),
                addr_of!(h_input[0]),
                H_INPUT_PUBLIC_KEY_SIZE_512,
            )
        });
        CycleCounter::end_measurement("PQM4 SHA3-256 (H_INPUT_PUBLIC_KEY_SIZE_512)", start);
    }

    {
        let mut h_input = [0u8; H_INPUT_PUBLIC_KEY_SIZE_768];
        rng.fill_bytes(&mut h_input);
        let start = CycleCounter::start_measurement();
        core::hint::black_box(libcrux_sha3::portable::sha256(&mut h_digest, &h_input));
        CycleCounter::end_measurement("libcrux SHA3-256 (H_INPUT_PUBLIC_KEY_SIZE_768)", start);

        let start = CycleCounter::start_measurement();
        core::hint::black_box(unsafe {
            libcrux_pqm4::sha3_256(
                addr_of_mut!(h_digest[0]),
                addr_of!(h_input[0]),
                H_INPUT_PUBLIC_KEY_SIZE_768,
            )
        });
        CycleCounter::end_measurement("PQM4 SHA3-256 (H_INPUT_PUBLIC_KEY_SIZE_768)", start);
    }

    {
        let mut h_input = [0u8; H_INPUT_PUBLIC_KEY_SIZE_1024];
        rng.fill_bytes(&mut h_input);
        let start = CycleCounter::start_measurement();
        core::hint::black_box(libcrux_sha3::portable::sha256(&mut h_digest, &h_input));
        CycleCounter::end_measurement("libcrux SHA3-256 (H_INPUT_PUBLIC_KEY_SIZE_1024)", start);

        let start = CycleCounter::start_measurement();
        core::hint::black_box(unsafe {
            libcrux_pqm4::sha3_256(
                addr_of_mut!(h_digest[0]),
                addr_of!(h_input[0]),
                H_INPUT_PUBLIC_KEY_SIZE_1024,
            )
        });
        CycleCounter::end_measurement("PQM4 SHA3-256 (H_INPUT_PUBLIC_KEY_SIZE_1024)", start);
    }

    // SHAKE256
    {
        let mut prf_input = [0u8; PRF_KDF.0];
        rng.fill_bytes(&mut prf_input);
        let mut prf_output = [0u8; PRF_KDF.1];
        let start = CycleCounter::start_measurement();
        core::hint::black_box(libcrux_sha3::portable::shake256(
            &mut prf_output,
            &prf_input,
        ));
        CycleCounter::end_measurement("libcrux SHAKE256 (PRF_KDF)", start);

        let start = CycleCounter::start_measurement();
        core::hint::black_box(unsafe {
            libcrux_pqm4::shake256(
                addr_of_mut!(prf_output[0]),
                PRF_KDF.1,
                addr_of!(prf_input[0]),
                PRF_KDF.0,
            )
        });
        CycleCounter::end_measurement("PQM4 SHAKE256 (PRF_KDF))", start);
    }
    {
        let mut prf_input = [0u8; PRF_IMPLICIT_REJECTION_SHARED_SECRET_512.0];
        rng.fill_bytes(&mut prf_input);
        let mut prf_output = [0u8; PRF_IMPLICIT_REJECTION_SHARED_SECRET_512.1];
        let start = CycleCounter::start_measurement();
        core::hint::black_box(libcrux_sha3::portable::shake256(
            &mut prf_output,
            &prf_input,
        ));
        CycleCounter::end_measurement(
            "libcrux SHAKE256 (PRF_IMPLICIT_REJECTION_SHARED_SECRET_512)",
            start,
        );

        let start = CycleCounter::start_measurement();
        core::hint::black_box(unsafe {
            libcrux_pqm4::shake256(
                addr_of_mut!(prf_output[0]),
                PRF_IMPLICIT_REJECTION_SHARED_SECRET_512.1,
                addr_of!(prf_input[0]),
                PRF_IMPLICIT_REJECTION_SHARED_SECRET_512.0,
            )
        });
        CycleCounter::end_measurement(
            "PQM4 SHAKE256 (PRF_IMPLICIT_REJECTION_SHARED_SECRET_512))",
            start,
        );
    }
    {
        let mut prf_input = [0u8; PRF_IMPLICIT_REJECTION_SHARED_SECRET_768.0];
        rng.fill_bytes(&mut prf_input);
        let mut prf_output = [0u8; PRF_IMPLICIT_REJECTION_SHARED_SECRET_768.1];
        let start = CycleCounter::start_measurement();
        core::hint::black_box(libcrux_sha3::portable::shake256(
            &mut prf_output,
            &prf_input,
        ));
        CycleCounter::end_measurement(
            "libcrux SHAKE256 (PRF_IMPLICIT_REJECTION_SHARED_SECRET_768)",
            start,
        );

        let start = CycleCounter::start_measurement();
        core::hint::black_box(unsafe {
            libcrux_pqm4::shake256(
                addr_of_mut!(prf_output[0]),
                PRF_IMPLICIT_REJECTION_SHARED_SECRET_768.1,
                addr_of!(prf_input[0]),
                PRF_IMPLICIT_REJECTION_SHARED_SECRET_768.0,
            )
        });
        CycleCounter::end_measurement(
            "PQM4 SHAKE256 (PRF_IMPLICIT_REJECTION_SHARED_SECRET_768))",
            start,
        );
    }
    {
        let mut prf_input = [0u8; PRF_IMPLICIT_REJECTION_SHARED_SECRET_1024.0];
        rng.fill_bytes(&mut prf_input);
        let mut prf_output = [0u8; PRF_IMPLICIT_REJECTION_SHARED_SECRET_1024.1];
        let start = CycleCounter::start_measurement();
        core::hint::black_box(libcrux_sha3::portable::shake256(
            &mut prf_output,
            &prf_input,
        ));
        CycleCounter::end_measurement(
            "SHAKE256 (PRF_IMPLICIT_REJECTION_SHARED_SECRET_1024)",
            start,
        );
    }

    {
        let mut prf_input = [0u8; PRF_ETA2_RANDOMNESS_512.0];
        rng.fill_bytes(&mut prf_input);
        let mut prf_output = [0u8; PRF_ETA2_RANDOMNESS_512.1];
        let start = CycleCounter::start_measurement();
        core::hint::black_box(libcrux_sha3::portable::shake256(
            &mut prf_output,
            &prf_input,
        ));
        CycleCounter::end_measurement("libcrux SHAKE256 (PRF_ETA2_RANDOMNESS_512)", start);

        let start = CycleCounter::start_measurement();
        core::hint::black_box(unsafe {
            libcrux_pqm4::shake256(
                addr_of_mut!(prf_output[0]),
                PRF_ETA2_RANDOMNESS_512.1,
                addr_of!(prf_input[0]),
                PRF_ETA2_RANDOMNESS_512.0,
            )
        });
        CycleCounter::end_measurement("PQM4 SHAKE256 (PRF_ETA2_RANDOMNESS_512))", start);
    }
    {
        let mut prf_input = [0u8; PRF_ETA2_RANDOMNESS_768.0];
        rng.fill_bytes(&mut prf_input);
        let mut prf_output = [0u8; PRF_ETA2_RANDOMNESS_768.1];
        let start = CycleCounter::start_measurement();
        core::hint::black_box(libcrux_sha3::portable::shake256(
            &mut prf_output,
            &prf_input,
        ));
        CycleCounter::end_measurement("libcrux SHAKE256 (PRF_ETA2_RANDOMNESS_768)", start);

        let start = CycleCounter::start_measurement();
        core::hint::black_box(unsafe {
            libcrux_pqm4::shake256(
                addr_of_mut!(prf_output[0]),
                PRF_ETA2_RANDOMNESS_768.1,
                addr_of!(prf_input[0]),
                PRF_ETA2_RANDOMNESS_768.0,
            )
        });
        CycleCounter::end_measurement("PQM4 SHAKE256 (PRF_ETA2_RANDOMNESS_768))", start);
    }
    {
        let mut prf_input = [0u8; PRF_ETA2_RANDOMNESS_1024.0];
        rng.fill_bytes(&mut prf_input);
        let mut prf_output = [0u8; PRF_ETA2_RANDOMNESS_1024.1];
        let start = CycleCounter::start_measurement();
        core::hint::black_box(libcrux_sha3::portable::shake256(
            &mut prf_output,
            &prf_input,
        ));
        CycleCounter::end_measurement("libcrux SHAKE256 (PRF_ETA2_RANDOMNESS_1024)", start);

        let start = CycleCounter::start_measurement();
        core::hint::black_box(unsafe {
            libcrux_pqm4::shake256(
                addr_of_mut!(prf_output[0]),
                PRF_ETA2_RANDOMNESS_1024.1,
                addr_of!(prf_input[0]),
                PRF_ETA2_RANDOMNESS_1024.0,
            )
        });
        CycleCounter::end_measurement("PQM4 SHAKE256 (PRF_ETA2_RANDOMNESS_1024))", start);
    }
    {
        let mut prf_input = [0u8; PRF_ETA1_RANDOMNESS_512.0];
        rng.fill_bytes(&mut prf_input);
        let mut prf_output = [0u8; PRF_ETA1_RANDOMNESS_512.1];
        let start = CycleCounter::start_measurement();
        core::hint::black_box(libcrux_sha3::portable::shake256(
            &mut prf_output,
            &prf_input,
        ));
        CycleCounter::end_measurement("libcrux SHAKE256 (PRF_ETA1_RANDOMNESS_512)", start);

        let start = CycleCounter::start_measurement();
        core::hint::black_box(unsafe {
            libcrux_pqm4::shake256(
                addr_of_mut!(prf_output[0]),
                PRF_ETA1_RANDOMNESS_512.1,
                addr_of!(prf_input[0]),
                PRF_ETA1_RANDOMNESS_512.0,
            )
        });
        CycleCounter::end_measurement("PQM4 SHAKE256 (PRF_ETA1_RANDOMNESS_512))", start);
    }
    {
        let mut prf_input = [0u8; PRF_ETA1_RANDOMNESS_768.0];
        rng.fill_bytes(&mut prf_input);
        let mut prf_output = [0u8; PRF_ETA1_RANDOMNESS_768.1];
        let start = CycleCounter::start_measurement();
        core::hint::black_box(libcrux_sha3::portable::shake256(
            &mut prf_output,
            &prf_input,
        ));
        CycleCounter::end_measurement("libcrux SHAKE256 (PRF_ETA1_RANDOMNESS_768)", start);

        let start = CycleCounter::start_measurement();
        core::hint::black_box(unsafe {
            libcrux_pqm4::shake256(
                addr_of_mut!(prf_output[0]),
                PRF_ETA1_RANDOMNESS_768.1,
                addr_of!(prf_input[0]),
                PRF_ETA1_RANDOMNESS_768.0,
            )
        });
        CycleCounter::end_measurement("PQM4 SHAKE256 (PRF_ETA1_RANDOMNESS_768))", start);
    }
    {
        let mut prf_input = [0u8; PRF_ETA1_RANDOMNESS_1024.0];
        rng.fill_bytes(&mut prf_input);
        let mut prf_output = [0u8; PRF_ETA1_RANDOMNESS_1024.1];
        let start = CycleCounter::start_measurement();
        core::hint::black_box(libcrux_sha3::portable::shake256(
            &mut prf_output,
            &prf_input,
        ));
        CycleCounter::end_measurement("libcrux SHAKE256 (PRF_ETA1_RANDOMNESS_1024)", start);

        let start = CycleCounter::start_measurement();
        core::hint::black_box(unsafe {
            libcrux_pqm4::shake256(
                addr_of_mut!(prf_output[0]),
                PRF_ETA1_RANDOMNESS_1024.1,
                addr_of!(prf_input[0]),
                PRF_ETA1_RANDOMNESS_1024.0,
            )
        });
        CycleCounter::end_measurement("PQM4 SHAKE256 (PRF_ETA1_RANDOMNESS_1024))", start);
    }

    // SHAKE128
    {
        let start = CycleCounter::start_measurement();
        let mut shake128_state =
            core::hint::black_box(libcrux_sha3::portable::incremental::shake128_init());
        CycleCounter::end_measurement("libcrux SHAKE128 Init", start);

        let mut shake128_state_pqm4 = libcrux_pqm4::shake128incctx { ctx: [0u64; 26] };
        let start = CycleCounter::start_measurement();
        core::hint::black_box(unsafe {
            libcrux_pqm4::shake128_inc_init(addr_of_mut!(shake128_state_pqm4))
        });
        CycleCounter::end_measurement("PQM4 SHAKE128 Init", start);
        {
            let mut init_absorb_final_input = [0u8; INIT_ABSORB_FINAL_INPUT_SIZE];
            rng.fill_bytes(&mut init_absorb_final_input);
            let start = CycleCounter::start_measurement();
            core::hint::black_box(libcrux_sha3::portable::incremental::shake128_absorb_final(
                &mut shake128_state,
                &init_absorb_final_input,
            ));
            CycleCounter::end_measurement("libcrux SHAKE128 Absorb final", start);

            let start = CycleCounter::start_measurement();
            core::hint::black_box(unsafe {
                libcrux_pqm4::shake128_inc_absorb(
                    addr_of_mut!(shake128_state_pqm4),
                    addr_of!(init_absorb_final_input[0]),
                    INIT_ABSORB_FINAL_INPUT_SIZE,
                )
            });
            core::hint::black_box(unsafe {
                libcrux_pqm4::shake128_inc_finalize(addr_of_mut!(shake128_state_pqm4))
            });
            CycleCounter::end_measurement("PQM4 SHAKE128 Absorb final", start);
        }

        {
            let mut one_block = [0u8; BLOCK_SIZE];
            rng.fill_bytes(&mut one_block);
            let start = CycleCounter::start_measurement();
            core::hint::black_box(
                libcrux_sha3::portable::incremental::shake128_squeeze_next_block(
                    &mut shake128_state,
                    &mut one_block,
                ),
            );
            CycleCounter::end_measurement("libcrux SHAKE128 Squeeze one block", start);

            let start = CycleCounter::start_measurement();
            core::hint::black_box(unsafe {
                libcrux_pqm4::shake128_inc_squeeze(
                    addr_of_mut!(one_block[0]),
                    BLOCK_SIZE,
                    addr_of_mut!(shake128_state_pqm4),
                )
            });
            CycleCounter::end_measurement("PQM4 SHAKE128 Squeeze one block", start);
        }

        {
            let mut three_blocks = [0u8; THREE_BLOCKS];
            rng.fill_bytes(&mut three_blocks);
            let start = CycleCounter::start_measurement();
            core::hint::black_box(
                libcrux_sha3::portable::incremental::shake128_squeeze_first_three_blocks(
                    &mut shake128_state,
                    &mut three_blocks,
                ),
            );
            CycleCounter::end_measurement("libcrux SHAKE128 Squeeze first three blocks", start);

            let start = CycleCounter::start_measurement();
            core::hint::black_box(unsafe {
                libcrux_pqm4::shake128_inc_squeeze(
                    addr_of_mut!(three_blocks[0]),
                    THREE_BLOCKS,
                    addr_of_mut!(shake128_state_pqm4),
                )
            });
            CycleCounter::end_measurement("PQM4 SHAKE128 Squeeze first three blocks", start);
        }
    }
    board::exit()
}
