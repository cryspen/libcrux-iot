/// Sponge construction — FIPS 202, Algorithm 8 (KECCAK[c])
/// with pad10*1 padding — FIPS 202, Algorithm 9.
///
/// FIPS 202 §3.1.2 places byte block `b` at lane `(x = b%5, y = b/5)`. With
/// the in-memory layout `state[5*x + y] = A[x, y]` (see `keccak_f.rs`),
/// byte block `b` therefore lives at `state[5*(b%5) + b/5]`.
use crate::createi;
use crate::keccak_f::{keccak_f, State};

/// Map a byte-block index `b ∈ 0..25` to the in-memory state slot that
/// holds the corresponding lane under the `state[5*x + y] = A[x, y]` layout.
///
/// FIPS 202 §3.1.2 puts byte block `b` at lane `(x = b%5, y = b/5)`.
#[inline]
#[hax_lib::requires(b < 25)]
fn byte_lane_idx(b: usize) -> usize {
    5 * (b % 5) + b / 5
}

#[cfg(hax)]
use hax_lib::int::*;

/// XOR a block of message bytes into the state (little-endian, lane-interleaved).
///
/// Corresponds to the `S ⊕ (Pi || 0^c)` step of Algorithm 8.
#[hax_lib::requires(rate <= 200 && rate % 8 == 0 && block.len() >= rate)]
pub fn xor_block_into_state(state: State, block: &[u8], rate: usize) -> State {
    // Iterate over state-array slots `idx = 5*x + y`. Slot `idx` corresponds
    // to byte block `b` where `idx = 5*(b%5) + b/5`, i.e. `b = 5*y + x` with
    // `x = idx/5`, `y = idx%5`.
    #[cfg(hax_backend_lean)] // https://github.com/AeneasVerif/aeneas/issues/924
    {
        core::array::from_fn(|idx| {
            let x = idx / 5;
            let y = idx % 5;
            let b = 5 * y + x;
            if b < rate / 8 {
                // The slice is exactly 8 bytes (since `b < rate / 8` and
                // `block.len() >= rate`), so `try_into::<[u8; 8]>` cannot fail.
                state[idx] ^ u64::from_le_bytes(block[8 * b..8 * b + 8].try_into().unwrap())
            } else {
                state[idx]
            }
        })
    }
    #[cfg(not(hax_backend_lean))]
    {
        createi(|idx| {
            let x = idx / 5;
            let y = idx % 5;
            let b = 5 * y + x;
            if b < rate / 8 {
                // The slice is exactly 8 bytes (since `b < rate / 8` and
                // `block.len() >= rate`), so `try_into::<[u8; 8]>` cannot fail.
                state[idx] ^ u64::from_le_bytes(block[8 * b..8 * b + 8].try_into().unwrap())
            } else {
                state[idx]
            }
        })
    }
}

/// Extract `len` bytes from the rate portion of the state (little-endian, lane-interleaved).
///
/// Corresponds to `Trunc_r(S)` in Algorithm 8.
#[hax_lib::requires(len <= 200 && output.len() >= len && out_offset <= output.len() - len)]
pub fn squeeze_state<const OUTPUT_LEN: usize>(
    state: &State,
    mut output: [u8; OUTPUT_LEN],
    out_offset: usize,
    len: usize,
) -> [u8; OUTPUT_LEN] {
    let bytes: [u8; 200] = createi(|i| state[byte_lane_idx(i / 8)].to_le_bytes()[i % 8]);
    output[out_offset..out_offset + len].copy_from_slice(&bytes[0..len]);
    output
}

/// Absorb one full block: XOR it into the state, then apply Keccak-f.
///
/// Corresponds to one iteration of the absorb loop in Algorithm 8 (step 6).
#[hax_lib::requires(rate <= 200 && rate % 8 == 0 && block.len() == rate)]
pub fn absorb_block(state: State, block: &[u8], rate: usize) -> State {
    let state = xor_block_into_state(state, block, rate);
    keccak_f(state)
}

/// Build the padded last block: copy remaining message bytes, add the
/// domain-separation byte `delim`, and set the final bit of pad10*1.
///
/// Returns a `rate`-byte buffer ready to be absorbed via `xor_block_into_state`.
#[hax_lib::requires(rate > 0 && rate <= 200 && rate % 8 == 0 && remaining < rate
                     && msg_offset <= message.len() && remaining <= message.len() - msg_offset)]
pub fn pad_last_block(
    message: &[u8],
    msg_offset: usize,
    remaining: usize,
    rate: usize,
    delim: u8,
) -> [u8; 200] {
    let mut buffer = [0u8; 200];
    buffer[0..remaining].copy_from_slice(&message[msg_offset..msg_offset + remaining]);
    buffer[remaining] = delim;
    buffer[rate - 1] = buffer[rate - 1] | 0x80;
    buffer
}

/// Absorb the final (possibly partial) block: pad it, XOR into state, and
/// apply Keccak-f.
///
/// Combines `pad_last_block` + `absorb_block`.
#[hax_lib::requires(rate > 0 && rate <= 200 && rate % 8 == 0 && remaining < rate
                     && msg_offset <= message.len() && remaining <= message.len() - msg_offset)]
pub fn absorb_final(
    state: State,
    message: &[u8],
    msg_offset: usize,
    remaining: usize,
    rate: usize,
    delim: u8,
) -> State {
    let block = pad_last_block(message, msg_offset, remaining, rate, delim);
    absorb_block(state, &block[0..rate], rate)
}

/// Recursively absorb the remaining bytes of `message`: peel off one full
/// `rate`-byte block, XOR it into the state, apply Keccak-f, then recurse on
/// the tail slice. Once fewer than `rate` bytes remain, pad and absorb the
/// partial final block.
#[hax_lib::requires(rate > 0 && rate <= 200 && rate % 8 == 0)]
#[hax_lib::decreases(message.len().to_int())]
pub fn absorb_rec(state: State, rate: usize, delim: u8, message: &[u8]) -> State {
    if message.len() < rate {
        absorb_final(state, message, 0, message.len(), rate, delim)
    } else {
        let state = absorb_block(state, &message[0..rate], rate);
        absorb_rec(state, rate, delim, &message[rate..])
    }
}

/// Absorb phase of the Keccak sponge (FIPS 202, Algorithm 8, step 6 combined
/// with the pad10*1 padding of Algorithm 9).
///
/// Splits `message` into `rate`-byte blocks, XORing each into the state and
/// applying Keccak-f. The final partial block is padded with the domain
/// separation byte `delim` and the pad10*1 terminator `0x80` before being
/// absorbed.
#[hax_lib::requires(rate > 0 && rate <= 200 && rate % 8 == 0)]
pub fn absorb(rate: usize, delim: u8, message: &[u8]) -> State {
    absorb_rec([0u64; 25], rate, delim, message)
}

/// Apply Keccak-f to `state` exactly `n` times.
#[hax_lib::decreases(n.to_int())]
pub fn iterate_keccak_f(n: usize, state: State) -> State {
    if n == 0 {
        state
    } else {
        keccak_f(iterate_keccak_f(n - 1, state))
    }
}

/// Squeeze phase of the Keccak sponge (FIPS 202, Algorithm 8, steps 8–9).
///
/// Extracts `OUTPUT_LEN` bytes from `state`, applying Keccak-f between each
/// `rate`-byte block of output.
///
/// Byteform definition: byte at position `k` lives in block `b = k / rate`
/// (or the trailing partial block if `b == OUTPUT_LEN / rate`); within a
/// block the offset is `j = k - b * rate`; the value is the `(j mod 8)`-th
/// little-endian byte of `iterate_keccak_f(b, state)`'s lane `(j / 8)`.
///
/// Equivalent to FIPS-202 Algorithm 8: for each full block apply keccak_f
/// and extract `rate` bytes; the trailing partial block uses one more
/// keccak_f before extracting `OUTPUT_LEN mod rate` bytes.
#[hax_lib::requires(rate > 0 && rate <= 200 && rate % 8 == 0 && OUTPUT_LEN < usize::MAX - 200)]
pub fn squeeze<const OUTPUT_LEN: usize>(state: State, rate: usize) -> [u8; OUTPUT_LEN] {
    createi(|k| {
        let b = k / rate;
        let j = k - b * rate;
        let state_b = iterate_keccak_f(b, state);
        state_b[byte_lane_idx(j / 8)].to_le_bytes()[j % 8]
    })
}

/// Keccak sponge — FIPS 202, Algorithm 8 combined with pad10*1 (Algorithm 9).
///
/// 1. Absorb: split `message` into `rate`-byte blocks, XOR each into the
///    state, and apply Keccak-f. The final partial block is padded with
///    the domain separation byte `delim` and the pad10*1 terminator `0x80`.
/// 2. Squeeze: extract `OUTPUT_LEN` bytes from the state, applying
///    Keccak-f between each `rate`-byte block of output.
///
/// The `OUTPUT_LEN < usize::MAX - 200` precondition is a Rust implementation
/// artifact to prevent arithmetic overflow; FIPS 202 places no upper bound
/// on the output length.
#[hax_lib::requires(rate > 0 && rate <= 200 && rate % 8 == 0 && OUTPUT_LEN < usize::MAX - 200)]
pub fn keccak<const OUTPUT_LEN: usize>(rate: usize, delim: u8, message: &[u8]) -> [u8; OUTPUT_LEN] {
    squeeze(absorb(rate, delim, message), rate)
}
