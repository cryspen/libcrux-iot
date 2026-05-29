/// Keccak-f[1600] permutation — FIPS 202, Section 3.3.
///
/// The state is a 5×5 array of 64-bit lanes stored as a flat `[u64; 25]`.
/// Lane `A[x, y]` maps to flat index `5*x + y`. This is an in-memory layout
/// choice independent of FIPS 202 §3.1.2's bit-string→array conversion;
/// θ/ρ/π/χ/ι operate on `A[x, y]` regardless of how the lanes are laid out.
/// The byte ↔ lane mapping in the sponge layer compensates so that the SHA-3
/// outputs remain FIPS-correct.
use crate::createi;

/// Keccak-f[1600] state: 5×5 lanes of 64-bit words.
/// Keccak state type, exposed for cross-crate verification.
pub type State = [u64; 25];

/// Read lane `A[x, y]`.
#[inline]
#[hax_lib::requires(x < 5 && y < 5)]
pub fn get(state: &State, x: usize, y: usize) -> u64 {
    state[5 * x + y]
}

// =========================================================================
// Constants — FIPS 202, Section 3.3 / Algorithm 5
// =========================================================================

/// Round constants `RC[ir]` for `ir = 0..23` — FIPS 202, Algorithm 5.
pub const ROUND_CONSTANTS: [u64; 24] = [
    0x0000_0000_0000_0001,
    0x0000_0000_0000_8082,
    0x8000_0000_0000_808A,
    0x8000_0000_8000_8000,
    0x0000_0000_0000_808B,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8009,
    0x0000_0000_0000_008A,
    0x0000_0000_0000_0088,
    0x0000_0000_8000_8009,
    0x0000_0000_8000_000A,
    0x0000_0000_8000_808B,
    0x8000_0000_0000_008B,
    0x8000_0000_0000_8089,
    0x8000_0000_0000_8003,
    0x8000_0000_0000_8002,
    0x8000_0000_0000_0080,
    0x0000_0000_0000_800A,
    0x8000_0000_8000_000A,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8080,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8008,
];

/// Rotation offsets for ρ step — FIPS 202, Algorithm 2 / Table 2.
///
/// Indexed as `RHO_OFFSETS[5*x + y]`.
pub const RHO_OFFSETS: [u32; 25] = [
    //  y=0  y=1  y=2  y=3  y=4
    0, 36, 3, 41, 18, // x = 0
    1, 44, 10, 45, 2, // x = 1
    62, 6, 43, 15, 61, // x = 2
    28, 55, 25, 21, 56, // x = 3
    27, 20, 39, 8, 14, // x = 4
];

// =========================================================================
// The five step mappings — FIPS 202, Algorithms 1–6
// =========================================================================

/// θ step — FIPS 202, Algorithm 1.
///
///   C[x]    = A[x,0] ⊕ A[x,1] ⊕ A[x,2] ⊕ A[x,3] ⊕ A[x,4]
///   D[x]    = C[x−1 mod 5] ⊕ rot(C[x+1 mod 5], 1)
///   A′[x,y] = A[x,y] ⊕ D[x]
pub fn theta(state: State) -> State {
    let c: [u64; 5] = createi(|x| {
        get(&state, x, 0)
            ^ get(&state, x, 1)
            ^ get(&state, x, 2)
            ^ get(&state, x, 3)
            ^ get(&state, x, 4)
    });
    let d: [u64; 5] = createi(|x| c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1));
    // Under the new layout `state[5*x + y] = A[x, y]`, the x-coordinate is
    // `idx / 5`.
    createi(|idx| state[idx] ^ d[idx / 5])
}

/// ρ step — FIPS 202, Algorithm 2.
///
///   A′[x,y] = rot(A[x,y], offset(x,y))
pub fn rho(state: State) -> State {
    createi(|idx| state[idx].rotate_left(RHO_OFFSETS[idx]))
}

/// π step — FIPS 202, Algorithm 3.
///
///   A′[x,y] = A[(x + 3y) mod 5, x]
pub fn pi(state: State) -> State {
    createi(|idx| {
        // Under the new layout `state[5*x + y] = A[x, y]`,
        // x = idx / 5, y = idx % 5.
        let x = idx / 5;
        let y = idx % 5;
        get(&state, (x + 3 * y) % 5, x)
    })
}

/// χ step — FIPS 202, Algorithm 4.
///
///   A′[x,y] = A[x,y] ⊕ (¬A[(x+1) mod 5, y] ∧ A[(x+2) mod 5, y])
pub fn chi(state: State) -> State {
    createi(|idx| {
        // Under the new layout `state[5*x + y] = A[x, y]`,
        // x = idx / 5, y = idx % 5.
        let x = idx / 5;
        let y = idx % 5;
        get(&state, x, y) ^ (!get(&state, (x + 1) % 5, y) & get(&state, (x + 2) % 5, y))
    })
}

/// ι step — FIPS 202, Algorithm 6.
///
///   A′[0,0] = A[0,0] ⊕ RC[ir]
#[hax_lib::requires(round < 24)]
pub fn iota(mut state: State, round: usize) -> State {
    state[0] ^= ROUND_CONSTANTS[round];
    state
}

// =========================================================================
// Unrolled step functions — straight-line forms for verification.
//
// These compute exactly the same values as `theta`/`rho`/`pi`/`chi` but
// avoid any `createi` closures, so Aeneas extracts them as plain
// `let … ← …; ok [s0, …, s24]` blocks (no `Vector.mapM`, no closure
// trait instances). They are the forms referenced by the Lean
// equivalence proof. Pure Rust tests below pin them to the `createi`
// versions so the two cannot drift.
// =========================================================================

/// θ step — straight-line (unrolled) form. Same value as `theta`.
pub fn theta_unrolled(state: State) -> State {
    // C[x] = A[x,0] ⊕ A[x,1] ⊕ A[x,2] ⊕ A[x,3] ⊕ A[x,4]
    //      = state[5x] ⊕ state[5x+1] ⊕ … ⊕ state[5x+4]
    let c0 = state[0] ^ state[1] ^ state[2] ^ state[3] ^ state[4];
    let c1 = state[5] ^ state[6] ^ state[7] ^ state[8] ^ state[9];
    let c2 = state[10] ^ state[11] ^ state[12] ^ state[13] ^ state[14];
    let c3 = state[15] ^ state[16] ^ state[17] ^ state[18] ^ state[19];
    let c4 = state[20] ^ state[21] ^ state[22] ^ state[23] ^ state[24];
    // D[x] = C[(x+4)%5] ⊕ rot(C[(x+1)%5], 1)
    let d0 = c4 ^ c1.rotate_left(1);
    let d1 = c0 ^ c2.rotate_left(1);
    let d2 = c1 ^ c3.rotate_left(1);
    let d3 = c2 ^ c4.rotate_left(1);
    let d4 = c3 ^ c0.rotate_left(1);
    // A'[x,y] = A[x,y] ⊕ D[x]; A'[5x+y] = state[5x+y] ⊕ d_x
    [
        state[0] ^ d0,
        state[1] ^ d0,
        state[2] ^ d0,
        state[3] ^ d0,
        state[4] ^ d0,
        state[5] ^ d1,
        state[6] ^ d1,
        state[7] ^ d1,
        state[8] ^ d1,
        state[9] ^ d1,
        state[10] ^ d2,
        state[11] ^ d2,
        state[12] ^ d2,
        state[13] ^ d2,
        state[14] ^ d2,
        state[15] ^ d3,
        state[16] ^ d3,
        state[17] ^ d3,
        state[18] ^ d3,
        state[19] ^ d3,
        state[20] ^ d4,
        state[21] ^ d4,
        state[22] ^ d4,
        state[23] ^ d4,
        state[24] ^ d4,
    ]
}

/// ρ step — straight-line (unrolled) form. Same value as `rho`.
pub fn rho_unrolled(state: State) -> State {
    [
        state[0].rotate_left(0),
        state[1].rotate_left(36),
        state[2].rotate_left(3),
        state[3].rotate_left(41),
        state[4].rotate_left(18),
        state[5].rotate_left(1),
        state[6].rotate_left(44),
        state[7].rotate_left(10),
        state[8].rotate_left(45),
        state[9].rotate_left(2),
        state[10].rotate_left(62),
        state[11].rotate_left(6),
        state[12].rotate_left(43),
        state[13].rotate_left(15),
        state[14].rotate_left(61),
        state[15].rotate_left(28),
        state[16].rotate_left(55),
        state[17].rotate_left(25),
        state[18].rotate_left(21),
        state[19].rotate_left(56),
        state[20].rotate_left(27),
        state[21].rotate_left(20),
        state[22].rotate_left(39),
        state[23].rotate_left(8),
        state[24].rotate_left(14),
    ]
}

/// π step — straight-line (unrolled) form. Same value as `pi`.
///
/// A'[x,y] = A[(x+3y) mod 5, x]
///   = state[5*((x+3y)%5) + x]
pub fn pi_unrolled(state: State) -> State {
    [
        state[0],  // (x=0,y=0): 5*0 + 0
        state[15], // (x=0,y=1): 5*3 + 0
        state[5],  // (x=0,y=2): 5*1 + 0
        state[20], // (x=0,y=3): 5*4 + 0
        state[10], // (x=0,y=4): 5*2 + 0
        state[6],  // (x=1,y=0): 5*1 + 1
        state[21], // (x=1,y=1): 5*4 + 1
        state[11], // (x=1,y=2): 5*2 + 1
        state[1],  // (x=1,y=3): 5*0 + 1
        state[16], // (x=1,y=4): 5*3 + 1
        state[12], // (x=2,y=0): 5*2 + 2
        state[2],  // (x=2,y=1): 5*0 + 2
        state[17], // (x=2,y=2): 5*3 + 2
        state[7],  // (x=2,y=3): 5*1 + 2
        state[22], // (x=2,y=4): 5*4 + 2
        state[18], // (x=3,y=0): 5*3 + 3
        state[8],  // (x=3,y=1): 5*1 + 3
        state[23], // (x=3,y=2): 5*4 + 3
        state[13], // (x=3,y=3): 5*2 + 3
        state[3],  // (x=3,y=4): 5*0 + 3
        state[24], // (x=4,y=0): 5*4 + 4
        state[14], // (x=4,y=1): 5*2 + 4
        state[4],  // (x=4,y=2): 5*0 + 4
        state[19], // (x=4,y=3): 5*3 + 4
        state[9],  // (x=4,y=4): 5*1 + 4
    ]
}

/// χ step — straight-line (unrolled) form. Same value as `chi`.
///
/// A'[x,y] = A[x,y] ⊕ (¬A[(x+1)%5, y] ∧ A[(x+2)%5, y])
///   = state[5x+y] ⊕ (¬state[5*((x+1)%5) + y] ∧ state[5*((x+2)%5) + y])
pub fn chi_unrolled(state: State) -> State {
    [
        state[0] ^ (!state[5] & state[10]),    // (x=0,y=0)
        state[1] ^ (!state[6] & state[11]),    // (x=0,y=1)
        state[2] ^ (!state[7] & state[12]),    // (x=0,y=2)
        state[3] ^ (!state[8] & state[13]),    // (x=0,y=3)
        state[4] ^ (!state[9] & state[14]),    // (x=0,y=4)
        state[5] ^ (!state[10] & state[15]),   // (x=1,y=0)
        state[6] ^ (!state[11] & state[16]),   // (x=1,y=1)
        state[7] ^ (!state[12] & state[17]),   // (x=1,y=2)
        state[8] ^ (!state[13] & state[18]),   // (x=1,y=3)
        state[9] ^ (!state[14] & state[19]),   // (x=1,y=4)
        state[10] ^ (!state[15] & state[20]),  // (x=2,y=0)
        state[11] ^ (!state[16] & state[21]),  // (x=2,y=1)
        state[12] ^ (!state[17] & state[22]),  // (x=2,y=2)
        state[13] ^ (!state[18] & state[23]),  // (x=2,y=3)
        state[14] ^ (!state[19] & state[24]),  // (x=2,y=4)
        state[15] ^ (!state[20] & state[0]),   // (x=3,y=0)
        state[16] ^ (!state[21] & state[1]),   // (x=3,y=1)
        state[17] ^ (!state[22] & state[2]),   // (x=3,y=2)
        state[18] ^ (!state[23] & state[3]),   // (x=3,y=3)
        state[19] ^ (!state[24] & state[4]),   // (x=3,y=4)
        state[20] ^ (!state[0] & state[5]),    // (x=4,y=0)
        state[21] ^ (!state[1] & state[6]),    // (x=4,y=1)
        state[22] ^ (!state[2] & state[7]),    // (x=4,y=2)
        state[23] ^ (!state[3] & state[8]),    // (x=4,y=3)
        state[24] ^ (!state[4] & state[9]),    // (x=4,y=4)
    ]
}

// =========================================================================
// Keccak-f[1600] — FIPS 202, Algorithm 7
// =========================================================================

/// Keccak-f[1600] permutation — FIPS 202, Algorithm 7.
///
///   Rnd(A, ir) = ι(χ(π(ρ(θ(A)))), ir)
pub fn keccak_f(mut state: State) -> State {
    for round in 0..24 {
        state = iota(chi(pi(rho(theta(state)))), round);
    }
    state
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn keccak_f_all_zeros() {
        // Known answer: after Keccak-f on the all-zero state, lane (0,0) has
        // a specific value that serves as a sanity check.
        let state = [0u64; 25];
        let result = keccak_f(state);
        assert_eq!(result[0], 0xF1258F7940E1DDE7);
    }

    #[test]
    fn keccak_f_all_ones() {
        let state = [0xFFFFFFFFFFFFFFFFu64; 25];
        let result = keccak_f(state);
        assert_ne!(result, state);
    }

    // ---------------------------------------------------------------------
    // Unrolled forms agree with the `createi` forms.
    // ---------------------------------------------------------------------

    fn random_state(seed: u64) -> State {
        // Tiny deterministic LCG — no rand dependency in the lib.
        let mut s = seed;
        core::array::from_fn(|_| {
            s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            s
        })
    }

    fn unroll_cases() -> [State; 5] {
        [
            [0u64; 25],
            [u64::MAX; 25],
            core::array::from_fn(|i| i as u64),
            random_state(0xABCDEF01),
            random_state(0xFEEDFACE),
        ]
    }

    #[test]
    fn theta_unrolled_matches_theta() {
        for s in unroll_cases() {
            assert_eq!(theta(s), theta_unrolled(s));
        }
    }

    #[test]
    fn rho_unrolled_matches_rho() {
        for s in unroll_cases() {
            assert_eq!(rho(s), rho_unrolled(s));
        }
    }

    #[test]
    fn pi_unrolled_matches_pi() {
        for s in unroll_cases() {
            assert_eq!(pi(s), pi_unrolled(s));
        }
    }

    #[test]
    fn chi_unrolled_matches_chi() {
        for s in unroll_cases() {
            assert_eq!(chi(s), chi_unrolled(s));
        }
    }
}
