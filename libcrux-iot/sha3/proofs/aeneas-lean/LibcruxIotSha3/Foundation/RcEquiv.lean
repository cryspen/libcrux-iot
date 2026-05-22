/-
  Round constant equivalence.

  The implementation stores each Keccak round constant as two 32-bit
  interleaved halves at indices 0..23 of `RC_INTERLEAVED_0` /
  `RC_INTERLEAVED_1`. The spec stores the full 64-bit constants at
  indices 0..23 of `ROUND_CONSTANTS`. We need the bit-interleaved
  combination of the two halves to equal the spec constant at every
  round.
-/
import LibcruxIotSha3.Foundation.Lift
import HacspecSha3

open Aeneas Aeneas.Std libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Foundation

/-- Auxiliary `Fin 24` form. Closed by `native_decide` after a `revert` —
    every concrete index reduces both sides to a closed `BitVec 64`
    literal which the kernel compares. The interleaved-RC and
    `ROUND_CONSTANTS` arrays are `@[irreducible]`, so the kernel
    `decide` reducer stalls; `native_decide` works through them via
    the compiled equational lemmas. -/
private theorem rc_equiv_aux (i : Fin 24) :
    lift_lane_bv
      (keccak.RC_INTERLEAVED_0.val[i.val]!).bv
      (keccak.RC_INTERLEAVED_1.val[i.val]!).bv =
    (keccak_f.ROUND_CONSTANTS.val[i.val]!).bv := by
  revert i; native_decide

/-- Round constant equivalence for `i : Nat` with `i < 24`. -/
theorem rc_equiv (i : Nat) (hi : i < 24) :
    lift_lane_bv
      (keccak.RC_INTERLEAVED_0.val[i]!).bv
      (keccak.RC_INTERLEAVED_1.val[i]!).bv =
    (keccak_f.ROUND_CONSTANTS.val[i]!).bv :=
  rc_equiv_aux ⟨i, hi⟩

end libcrux_iot_sha3.Foundation
