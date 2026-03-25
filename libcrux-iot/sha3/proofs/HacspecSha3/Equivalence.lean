import HacspecSha3.Funs
import LibcruxIotSha3.Funs



/-! ## Lift: Interleaved Lane2U32 → standard u64

The implementation stores each 64-bit Keccak lane as two u32 values in
bit-interleaved form: `_0[0]` holds even-indexed bits, `_0[1]` holds
odd-indexed bits. We reconstruct the standard u64 by spreading these
bits back to their natural positions.
-/

/-- Spread 32 bits into even positions of a 64-bit value.
    Bit k of input → bit 2k of output. -/
def spread_to_even (x : BitVec 32) : BitVec 64 :=
  let x : BitVec 64 := x.zeroExtend 64
  let x := (x ||| (x <<< 16)) &&& 0x0000ffff0000ffff#64
  let x := (x ||| (x <<<  8)) &&& 0x00ff00ff00ff00ff#64
  let x := (x ||| (x <<<  4)) &&& 0x0f0f0f0f0f0f0f0f#64
  let x := (x ||| (x <<<  2)) &&& 0x3333333333333333#64
  let x := (x ||| (x <<<  1)) &&& 0x5555555555555555#64
  x

/-- Reconstruct a u64 from interleaved zeta components.
    Bit 2k of result = bit k of z0 (even bits),
    bit 2k+1 of result = bit k of z1 (odd bits). -/
def lift_lane_bv (z0 z1 : BitVec 32) : BitVec 64 :=
  spread_to_even z0 ||| (spread_to_even z1 <<< 1)

def lift_lane (l : libcrux_iot_sha3.lane.Lane2U32) : Aeneas.Std.U64 :=
  ⟨lift_lane_bv l[0].bv l[1].bv⟩

def lift (s : libcrux_iot_sha3.state.KeccakState) : Aeneas.Std.Array Aeneas.Std.U64 25#usize :=
  ⟨.ofFn fun i : Fin 25 => lift_lane s.st[i], by simp⟩


/-! ## Top-level equivalence -/

open Std.Do in
theorem equivalence (s : libcrux_iot_sha3.state.KeccakState) (hi : s.i = 0#usize) :
    ⦃ ⌜ True ⌝ ⦄
    do let r_impl ← libcrux_iot_sha3.keccak.keccakf1600 s
       let r_spec ← hacspec_sha3.keccak_f.keccak_f (lift s)
       pure (r_spec = lift r_impl)
    ⦃ ⇓ r => ⌜ r ⌝ ⦄ := by
  sorry
