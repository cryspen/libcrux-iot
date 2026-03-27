import extraction.hacspec_sha3
import extraction.libcrux_iot_sha3

open libcrux_iot_sha3.lane libcrux_iot_sha3.state

/-! ## Lifting definitions: bit-interleaved u32 pairs → standard u64

The Keccak implementation uses a "bit-interleaved" lane representation: each 64-bit
lane is stored as a pair of 32-bit words `(z0, z1)` where `z0` holds even-indexed bits
and `z1` holds odd-indexed bits. The reference spec uses standard 64-bit integers.

These definitions bridge the two representations:
- `spread_to_even`: maps 32 consecutive bits to 64 bits at even positions
- `lift_lane_bv`: reconstructs a 64-bit lane from interleaved halves
- `lift`: lifts the full 25-lane state from interleaved to standard form
- `impl_perm`: the lane permutation applied by the impl's pi step
- `lift_perm`: lifts a permuted state

The `spread_to_even` / `lift_lane_bv` functions are marked `@[local irreducible]` in
proof files after algebraic lifting lemmas are proven. This is critical for performance:
without irreducibility, simp unfolds them into 6-step 64-bit operations × 25 lanes,
causing multi-GB term blowup.
-/

/-- Spread 32 bits into the even bit positions of a 64-bit word.
    bit[i] of input → bit[2i] of output. Uses a standard parallel bit-deposit sequence. -/
def spread_to_even (x : BitVec 32) : BitVec 64 :=
  let x : BitVec 64 := x.zeroExtend 64
  let x := (x ||| (x <<< 16)) &&& 0x0000ffff0000ffff#64
  let x := (x ||| (x <<<  8)) &&& 0x00ff00ff00ff00ff#64
  let x := (x ||| (x <<<  4)) &&& 0x0f0f0f0f0f0f0f0f#64
  let x := (x ||| (x <<<  2)) &&& 0x3333333333333333#64
  let x := (x ||| (x <<<  1)) &&& 0x5555555555555555#64
  x

/-- Reconstruct a standard 64-bit lane from its interleaved halves.
    z0 holds even-indexed bits, z1 holds odd-indexed bits. -/
def lift_lane_bv (z0 z1 : BitVec 32) : BitVec 64 :=
  spread_to_even z0 ||| (spread_to_even z1 <<< 1)

/-- Lift one interleaved Lane2U32 to a standard u64. -/
def lift_lane (l : Lane2U32) : u64 :=
  UInt64.ofBitVec (lift_lane_bv l._0.toVec[0].toBitVec l._0.toVec[1].toBitVec)

/-- Lift the full 25-lane Keccak state from interleaved to standard representation. -/
def lift (s : KeccakState) : RustArray u64 25 :=
  RustArray.ofVec (.ofFn fun i => lift_lane s.st.toVec[i])

/-- The lane permutation applied by the implementation's pi step.
    Maps lane index (5x + z) → (5x + (3z + 2x) mod 5), matching the Keccak pi permutation. -/
def impl_perm (i : Fin 25) : Fin 25 :=
  let x := i.val / 5; let z := i.val % 5; ⟨5 * x + (3 * z + 2 * x) % 5, by omega⟩

/-- Lift a permuted state: applies permutation p to lane indices before lifting. -/
def lift_perm (s : KeccakState) (p : Fin 25 → Fin 25) : RustArray u64 25 :=
  RustArray.ofVec (.ofFn fun i => lift_lane s.st.toVec[(p i).val])

/-- 32-bit rotation abbreviation used in the interleaved implementation. -/
abbrev rot32 (x : u32) (n : Nat) : u32 :=
  UInt32.ofBitVec (BitVec.rotateLeft x.toBitVec n)
