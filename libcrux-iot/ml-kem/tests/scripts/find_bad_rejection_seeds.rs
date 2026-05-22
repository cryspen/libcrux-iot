//! Bad-seed generator for the `rejection_sampling_pressure` test module.
//!
//! Status: SKETCH. Not auto-compiled by `cargo test` (this file lives under
//! `tests/scripts/` which Cargo doesn't pick up as a `[[test]]` target).
//! To run, copy into `examples/` or wire as a `[[bin]]`.
//!
//! Purpose: enumerate seeds for which `hacspec_ml_kem::sampling::sample_ntt`
//! requires more than one 168-byte SHAKE128 block to fill a 256-coefficient
//! ring element. These "unlucky" seeds force the impl's
//! `sample_from_xof` into its `while !done` multi-block branch, exercising
//! the block-iteration path that the deterministic first-block path skips.
//!
//! ## Detection strategy
//!
//! The spec's `sample_ntt::<70, 560, 840, 6720>` consumes a buffer of 840
//! random bytes (5 × 168 = first 5 blocks) and either fills 256 coefficients
//! or returns `BadRejectionSamplingRandomnessError`. We treat any seed for
//! which the **first** 168 bytes alone are insufficient as "unlucky".
//!
//! Strict detection of "needs > 1 block" without modifying spec sources:
//!   1. Compute the SHAKE128 expansion of the seed (with the matrix-coords
//!      domain-separation suffix the spec uses internally).
//!   2. Pass only the first 168 bytes to a length-bounded variant of
//!      `rej_sample_step` and check whether 256 coefficients accumulate.
//!
//! For simplicity here we approximate: run the spec's `sample_ntt` on the
//! first 168 bytes (padded with zeros), and if it succeeds, the seed is
//! "easy"; if it fails, the seed is "unlucky" — i.e. a real run would have
//! needed > 1 block of SHAKE128 output.
//!
//! ## Usage
//!
//! Once promoted to a `[[bin]]` or `[[example]]`:
//!
//! ```bash
//! cargo run --example find_bad_rejection_seeds -- mlkem768
//! ```
//!
//! Emits a `const MLKEM_NNN_UNLUCKY: [[u8; 64]; 5] = [...]` block ready to
//! paste into `tests/cross_spec.rs::rejection_sampling_pressure`.

#![allow(dead_code)]

use rand::{Rng, SeedableRng};
use rand::rngs::StdRng;

/// One single-block "rejection check": treat the first 168 bytes as the
/// only available SHAKE128 output and ask the spec to fill a ring element.
/// Returns `true` if more than one block would be needed.
fn needs_more_than_one_block(_shake128_first_168_bytes: &[u8; 168]) -> bool {
    // NOTE: the spec's `sample_ntt` signature requires a full
    // `[u8; N12]` buffer (e.g. 840 bytes for 5 blocks). To do "single
    // block only", we'd pad with zeros and check failure.  The fully
    // wired call is:
    //
    //   let mut buf = [0u8; 840];
    //   buf[..168].copy_from_slice(shake128_first_168_bytes);
    //   hacspec_ml_kem::sampling::sample_ntt::<70, 560, 840, 6720>(buf).is_err()
    //
    // BUT this is approximate: zero-padding might coincidentally let the
    // sampler succeed (zeros are accepted as valid coefficients).
    //
    // A precise version requires either:
    //   (a) Re-implementing rej_sample_step counting in this script, or
    //   (b) Exposing a "consumed_blocks" hook on the spec sampler.
    //
    // For now: leave this stub and emit an empty table. The proptest layer
    // with `PROPTEST_CASES=128+` provides incidental multi-block coverage.
    false
}

fn shake128_expand(seed: &[u8; 64], _matrix_i: u8, _matrix_j: u8) -> [u8; 168] {
    // Real implementation: call libcrux_iot_sha3::shake128_ema with a
    // 34-byte input: seed[..32] ++ [matrix_i, matrix_j].
    // Stub for the script skeleton.
    let mut out = [0u8; 168];
    for (i, byte) in seed.iter().enumerate() {
        out[i % 168] ^= byte;
    }
    out
}

fn main() {
    let variant = std::env::args().nth(1).unwrap_or_else(|| "mlkem768".into());
    eprintln!("Searching for unlucky seeds for {} ...", variant);

    let mut rng = StdRng::seed_from_u64(0xML_KEM_BAD_SEEDS);
    let mut found: Vec<[u8; 64]> = vec![];
    let target = 5usize;
    let mut tried = 0u64;

    while found.len() < target && tried < 1_000_000 {
        let mut seed = [0u8; 64];
        rng.fill(&mut seed);
        let expanded = shake128_expand(&seed, 0, 0);
        if needs_more_than_one_block(&expanded) {
            found.push(seed);
        }
        tried += 1;
        if tried % 10_000 == 0 {
            eprintln!("  tried {} seeds, found {}", tried, found.len());
        }
    }

    println!("const {}_UNLUCKY: [[u8; 64]; {}] = [", variant.to_uppercase(), found.len());
    for s in &found {
        print!("    [");
        for (i, b) in s.iter().enumerate() {
            if i > 0 { print!(", "); }
            print!("0x{:02x}", b);
        }
        println!("],");
    }
    println!("];");

    if found.is_empty() {
        eprintln!("\nNOTE: detection stub did not surface any seeds. See the");
        eprintln!("module comment for the precise detection wiring required.");
    }
}
