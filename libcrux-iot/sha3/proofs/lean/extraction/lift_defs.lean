import extraction.hacspec_sha3
import extraction.libcrux_iot_sha3

open libcrux_iot_sha3.lane libcrux_iot_sha3.state

/-! ## Lift definitions: interleaved Lane2U32 → standard u64 -/

def spread_to_even (x : BitVec 32) : BitVec 64 :=
  let x : BitVec 64 := x.zeroExtend 64
  let x := (x ||| (x <<< 16)) &&& 0x0000ffff0000ffff#64
  let x := (x ||| (x <<<  8)) &&& 0x00ff00ff00ff00ff#64
  let x := (x ||| (x <<<  4)) &&& 0x0f0f0f0f0f0f0f0f#64
  let x := (x ||| (x <<<  2)) &&& 0x3333333333333333#64
  let x := (x ||| (x <<<  1)) &&& 0x5555555555555555#64
  x

def lift_lane_bv (z0 z1 : BitVec 32) : BitVec 64 :=
  spread_to_even z0 ||| (spread_to_even z1 <<< 1)

def lift_lane (l : Lane2U32) : u64 :=
  UInt64.ofBitVec (lift_lane_bv l._0.toVec[0].toBitVec l._0.toVec[1].toBitVec)

def lift (s : KeccakState) : RustArray u64 25 :=
  RustArray.ofVec (.ofFn fun i => lift_lane s.st.toVec[i])

def impl_perm (i : Fin 25) : Fin 25 :=
  let x := i.val / 5; let z := i.val % 5; ⟨5 * x + (3 * z + 2 * x) % 5, by omega⟩

def lift_perm (s : KeccakState) (p : Fin 25 → Fin 25) : RustArray u64 25 :=
  RustArray.ofVec (.ofFn fun i => lift_lane s.st.toVec[(p i).val])

abbrev rot32 (x : u32) (n : Nat) : u32 :=
  UInt32.ofBitVec (BitVec.rotateLeft x.toBitVec n)
