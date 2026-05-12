/-
  Bit-interleaved → standard `u64` lifting.

  The implementation stores each 64-bit Keccak lane as two 32-bit halves
  in bit-interleaved form:
    z0 holds even-indexed bits, z1 holds odd-indexed bits.

  These definitions reconstruct the standard 64-bit lane and lift the
  full 25-lane state to the spec's `Array Std.U64 25#usize`.

  After M1, the impl and spec agree on the lane index convention
  (`A[x, y]` at flat index `5*x + y`), so `lift` is identity on indices —
  no permutation is needed.

  `spread_to_even` and `lift_lane_bv` are marked `@[irreducible]` after
  the bv_decide lifting algebra in `LiftLemmas.lean` is proven; without
  this guard, every later simp pass unfolds them into a six-step parallel
  bit-deposit sequence × 25 lanes, blowing up term sizes by orders of
  magnitude.
-/
import LibcruxIotSha3.Extraction.Funs

open Aeneas Aeneas.Std

namespace libcrux_iot_sha3.Equivalence

/-- The interleaved lane representation has a canonical default
    (both halves zero) — needed for the `_!` accessors used below. -/
instance : Inhabited libcrux_iot_sha3.lane.Lane2U32 :=
  ⟨⟨[0#u32, 0#u32], by decide⟩⟩

/-- Spread 32 bits into the even bit positions of a 64-bit word.
    Bit `i` of the input lands at bit `2*i` of the output. -/
def spread_to_even (x : BitVec 32) : BitVec 64 :=
  let x : BitVec 64 := x.zeroExtend 64
  let x := (x ||| (x <<< 16)) &&& 0x0000ffff0000ffff#64
  let x := (x ||| (x <<<  8)) &&& 0x00ff00ff00ff00ff#64
  let x := (x ||| (x <<<  4)) &&& 0x0f0f0f0f0f0f0f0f#64
  let x := (x ||| (x <<<  2)) &&& 0x3333333333333333#64
  let x := (x ||| (x <<<  1)) &&& 0x5555555555555555#64
  x

/-- Reconstruct a 64-bit lane from interleaved halves: bit `2k` from `z0`,
    bit `2k+1` from `z1`. -/
def lift_lane_bv (z0 z1 : BitVec 32) : BitVec 64 :=
  spread_to_even z0 ||| (spread_to_even z1 <<< 1)

/-- Lift one interleaved `Lane2U32` to a standard `Std.U64`. -/
def lift_lane (l : libcrux_iot_sha3.lane.Lane2U32) : Std.U64 :=
  ⟨lift_lane_bv (l.val[0]!).bv (l.val[1]!).bv⟩

/-- Lift the full 25-lane Keccak state from interleaved to standard form.

    After M1, this is identity-on-indices: `(lift s).val[i]! = lift_lane (s.st.val[i]!)`. -/
def lift (s : libcrux_iot_sha3.state.KeccakState) : Array Std.U64 25#usize :=
  ⟨List.ofFn (fun i : Fin 25 => lift_lane (s.st.val[i.val]!)),
    by simp⟩

/-! ## 32-bit rotation abbreviation used in the interleaved implementation -/

abbrev rot32 (x : Std.U32) (n : Nat) : Std.U32 :=
  ⟨x.bv.rotateLeft n⟩

/-! ## The permutation that the impl applies implicitly through addressing.

    The implementation performs π as a *storage relabeling*: each round
    reads from different physical positions, so after one round the
    canonical `st[5*x + y] ↔ A[x, y]` mapping no longer holds. The
    cycle has order 4 — every 4 rounds the lane layout re-aligns with
    the spec.
-/

/-- The lane permutation induced by one round of the implementation.
    Maps an impl lane index to the spec position it now holds:
    `impl_perm(5*x + z) = 5*x + ((3*z + 2*x) mod 5)`. -/
def impl_perm (i : Fin 25) : Fin 25 :=
  let x := i.val / 5
  let z := i.val % 5
  ⟨5 * x + (3 * z + 2 * x) % 5, by omega⟩

/-- The impl permutation has order 4: after 4 rounds, layout re-aligns
    with the spec's `[u64; 25]` ordering. Closed by `decide` over the 25
    indices. -/
theorem impl_perm_pow4_eq_id :
    ∀ i : Fin 25, impl_perm (impl_perm (impl_perm (impl_perm i))) = i := by
  decide

/-- Lift a permuted state: applies permutation `p` to lane indices before
    lifting each lane. -/
def lift_perm (s : libcrux_iot_sha3.state.KeccakState) (p : Fin 25 → Fin 25) :
    Array Std.U64 25#usize :=
  ⟨List.ofFn (fun i : Fin 25 => lift_lane (s.st.val[(p i).val]!)),
    by simp⟩

/-- `lift_perm s id = lift s`. -/
theorem lift_perm_id (s : libcrux_iot_sha3.state.KeccakState) :
    lift_perm s id = lift s := by
  unfold lift_perm lift
  rfl

end libcrux_iot_sha3.Equivalence
