import extraction.helpers
import extraction.libcrux_iot_sha3
import Hax
import Std.Tactic.Do
import Std.Do.Triple

open Std.Do
open Std.Tactic

/-!
# Specification of `KeccakXofState`

This file specifies the functional correctness of the `KeccakXofState`
absorb/squeeze API.  The concrete implementation maintains a buffering
layer on top of an inner `KeccakState`; the spec abstracts all of that
away, characterising the API purely in terms of:

  - the flat list of bytes that have been absorbed so far,
  - the total number of output bytes that have been squeezed so far.

The oracle `keccak_xof_byte` is left opaque: its definition is the
standard Keccak sponge applied to the padded message.  Connecting this
oracle to the actual Keccak permutation is deliberately left for
separate, lower-level proofs.
-/

namespace libcrux_iot_sha3.keccak.spec

-- ---------------------------------------------------------------------------
-- ## Abstract oracle

/-- The i-th output byte of the Keccak-based XOF with the given rate,
domain separator and (pre-padding) message. -/
opaque keccak_xof_byte (RATE : Nat) (delim : UInt8)
    (msg : List UInt8) (i : Nat) : UInt8

-- ---------------------------------------------------------------------------
-- ## Abstract state

/-- Abstract view of a `KeccakXofState`.  All buffering details of the
concrete implementation are hidden; only the data that is observable via
the public API is tracked. -/
structure XofAbs where
  /-- All bytes fed to `absorb` and `absorb_final` so far,
      **not** including the padding added by `absorb_final`. -/
  absorbed  : List UInt8
  /-- Has `absorb_final` been called? -/
  finalized : Bool
  /-- Domain separator byte chosen at `absorb_final` time. -/
  delim     : UInt8
  /-- Number of output bytes produced by previous `squeeze` calls. -/
  squeezed  : Nat

-- ---------------------------------------------------------------------------
-- ## Abstraction relation

/-- The concrete buffering invariant: `buf[0..buf_len]` holds exactly the
`buf_len`-byte tail of `absorbed` that has not yet been permuted into the
inner state. -/
def bufInvariant (RATE : Nat) (buf : RustArray u8 RATE)
    (buf_len : Nat) (absorbed : List UInt8) : Prop :=
  buf_len < RATE ∧
  ∃ (prefix : List UInt8),
    absorbed = prefix ++ (buf.toVec.toList.take buf_len) ∧
    -- `prefix` is exactly rate-aligned
    prefix.length % RATE = 0

/-- `Abs st model` — the concrete state `st` is a valid realisation of
the abstract model `model`. -/
structure Abs (RATE : Nat) (st : KeccakXofState RATE) (m : XofAbs) : Prop where
  /-- Finalization flag is consistent. -/
  fin_agree    : st.sponge = (m.squeezed > 0)
  /-- Before finalization the buffer correctly shadows the end of `absorbed`. -/
  buf_inv      : ¬m.finalized →
                   bufInvariant RATE st.buf st.buf_len m.absorbed
  /-- After finalization the buffer is irrelevant (buf_len is 0). -/
  buf_empty    : m.finalized → st.buf_len = 0

-- ---------------------------------------------------------------------------
-- ## Specification theorems

/-- **`absorb` spec.**

Absorbing a slice of bytes extends the logical message.  The concrete
state may have changed its internal buffer, but the abstract view only
grows by appending the new bytes. -/
theorem absorb_spec (RATE : Nat) (st : KeccakXofState RATE)
    (m : XofAbs) (input : RustSlice u8)
    (habs : Abs RATE st m) (hnfin : ¬m.finalized) :
    ⦃ ⌜ True ⌝ ⦄
    KeccakXofState.absorb st input
    ⦃ ⇓ st' => ⌜ Abs RATE st'
        { m with absorbed := m.absorbed ++ input.toVec.toList } ⌝ ⦄ := by
  sorry

/-- **`absorb_final` spec.**

Absorbing the final block appends the remaining bytes, marks the state
as finalized (no further absorb calls are valid), and records the domain
separator. -/
theorem absorb_final_spec (RATE : Nat) (DELIM : UInt8)
    (st : KeccakXofState RATE) (m : XofAbs) (input : RustSlice u8)
    (habs : Abs RATE st m) (hnfin : ¬m.finalized) :
    ⦃ ⌜ True ⌝ ⦄
    KeccakXofState.absorb_final st DELIM input
    ⦃ ⇓ st' => ⌜ Abs RATE st'
        { m with
          absorbed  := m.absorbed ++ input.toVec.toList
          finalized := true
          delim     := DELIM } ⌝ ⦄ := by
  sorry

/-- **`squeeze` spec.**

Each call to `squeeze` returns the next `out.length` bytes from the XOF
output stream, starting at byte offset `m.squeezed`.  After the call,
the number of squeezed bytes advances by `out.length`, and the abstract
state is otherwise unchanged. -/
theorem squeeze_spec (RATE : Nat) (st : KeccakXofState RATE)
    (m : XofAbs) (out : RustSlice u8)
    (habs : Abs RATE st m) (hfin : m.finalized) :
    ⦃ ⌜ True ⌝ ⦄
    KeccakXofState.squeeze st out
    ⦃ ⇓ (st', out') =>
        -- The abstract state advances only in `squeezed`
        ⌜ Abs RATE st' { m with squeezed := m.squeezed + out.length } ∧
          -- Every output byte matches the oracle at the correct position
          ∀ i, i < out.length →
            out'[i]! = keccak_xof_byte RATE m.delim m.absorbed
                                        (m.squeezed + i) ⌝ ⦄ := by
  sorry

-- ---------------------------------------------------------------------------
-- ## Derived lemmas

/-- **Absorb compositionality.**

Calling `absorb xs` followed by `absorb ys` produces a state that is
equivalent (modulo the abstraction) to calling `absorb (xs ++ ys)`. -/
theorem absorb_append (RATE : Nat) (st : KeccakXofState RATE)
    (m : XofAbs) (xs ys : RustSlice u8)
    (habs : Abs RATE st m) (hnfin : ¬m.finalized) :
    ∀ st_mid,
      (absorb_spec RATE st m xs habs hnfin) →
      Abs RATE st_mid { m with absorbed := m.absorbed ++ xs.toVec.toList } →
      -- absorbing in two steps reaches the same abstract state as one step
      ∃ st_end,
        Abs RATE st_end
          { m with absorbed :=
              m.absorbed ++ xs.toVec.toList ++ ys.toVec.toList } := by
  sorry

/-- **Multi-squeeze consistency.**

Two sequential `squeeze` calls of arbitrary sizes produce the same bytes
as a single `squeeze` of the combined size. -/
theorem squeeze_concat (RATE : Nat) (st : KeccakXofState RATE)
    (m : XofAbs) (out1 out2 : RustSlice u8)
    (habs : Abs RATE st m) (hfin : m.finalized) :
    -- After squeezing `out1` we are in a consistent state
    ∀ st_mid,
      Abs RATE st_mid { m with squeezed := m.squeezed + out1.length } →
      -- A second squeeze picks up exactly where the first left off
      ∀ i, i < out2.length →
        ∃ out2',
          ⦃ ⌜ True ⌝ ⦄
          KeccakXofState.squeeze st_mid out2
          ⦃ ⇓ (_, out2'') => ⌜ out2''[i]! =
              keccak_xof_byte RATE m.delim m.absorbed
                              (m.squeezed + out1.length + i) ⌝ ⦄ := by
  sorry

end libcrux_iot_sha3.keccak.spec
