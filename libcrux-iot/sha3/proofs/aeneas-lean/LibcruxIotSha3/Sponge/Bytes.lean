/-
  # Phase 1a — Byte ↔ Lane primitives (`load_block`, `store_block`,
  # `load_block_full`).

  This file is the bit-level interleave ↔ LE byte bridge for the sponge
  campaign. It is intended to host three `@[spec]` Triples bridging:
  - `state.KeccakState.load_block`      ↔ `sponge.xor_block_into_state`
  - `state.KeccakState.store_block`     ↔ per-byte projection of `lift s`
  - `state.KeccakState.load_block_full` ↔ `load_block` after slice coercion

  ## Phase 1a status: load-bearing helper lemma only (DEFERRED Triples)

  The three Triples described in Plan.lean § 1 are **not installed yet**;
  this file delivers only the load-bearing bit-level helper lemma
  `lift_lane_bv_xor` (which is the structural anchor for the eventual
  real posts) and the import scaffold so downstream `Sponge/` files can
  begin to depend on the namespace.

  ### Why deferred

  After spinning up `hax_mvcgen` on `state.KeccakState.load_block`, the
  goal reduces to a `wp⟦Slice.len blocks⟧` chained through `massert
  (RATE ≤ ·)`, `massert (RATE % 8 = 0)`, and two `state.load_block_2u32_loop{0,1}`
  invocations.  There is **no prior precedent in `LibcruxIotSha3/`** for
  any of the following sub-specs:

  * `@[spec]` for `core_models.slice.Slice.len` returning the underlying
    list length.
  * `@[spec]` characterizations of `massert` (or a Triple-level unfolding
    pattern that interacts with `hax_mvcgen` cleanly).
  * `@[spec]` characterizations of `core_models.slice.Slice.index` over
    a `Range Usize` (used by Loop A to read 4-byte windows of `blocks`).
  * `@[spec]` for `try_from` + `Result.unwrap` (used to convert
    `Slice U8 → Array U8 4#usize`).
  * `@[spec]` for `core_models.num.U32.from_le_bytes`, `U32.to_le_bytes`,
    `U64.from_le_bytes`, `U64.to_le_bytes`.
  * `@[spec]` for `core_models.slice.Slice.copy_from_slice` (used by
    `store_block` to write u32 halves back to `out`).
  * `@[spec]` for `core_models.Slice.Insts.Core_modelsOpsIndexIndexMut.index_mut`
    (the mutable-slice access used by Loop A of `store_block`).
  * A `loop_range_spec_usize`-driven Triple for each of the two loops in
    `state.load_block_2u32` and the one loop in `state.store_block_2u32`.
  * A `createi 25` Triple for `sponge.xor_block_into_state`'s
    *conditional* closure (the `b < rate/8` branch — the existing
    `createi_pure_spec` only covers state-preserving pure closures, but
    this closure IS state-preserving so it should still apply; the
    branching is over the input not the state, so `createi_pure_spec`
    likely covers it after suitable per-closure spec).

  Each of these is itself a small but non-trivial Triple — together they
  represent ~3.0 lemma-units of effort per Plan.lean's roll-up.

  ### What this file does deliver

  - `lift_lane_bv_xor` — the BV-level distributivity of `lift_lane_bv`
    over per-half XOR.  Proven by `bv_decide`.  This is one half of the
    `interleave_xor_lift_eq` bridge described in Plan.lean line 222.
  - The file-template (header, namespace, opaque-seal re-issue) so
    downstream phases can begin importing `Sponge.Bytes` and adding
    their own scaffolding.

  ## See also

  - `LibcruxIotSha3/Sponge/Plan.lean` § 1 — full Plan.
  - `LibcruxIotSha3/Sponge/Opaque.lean` — Phase 0 seal of `keccakf1600`.
  - `LibcruxIotSha3/Equivalence/HacspecBridge.lean` — `createi_pure_spec`,
    `result_eq_of_triple`, `close_array25` macros, `usize_bv_ofNat_val`,
    `loop_range_spec_usize`, `IteratorRange_next_spec_usize`.
  - `LibcruxIotSha3/Equivalence/Lift.lean` — `lift`, `lift_lane`,
    `lift_lane_bv`, `spread_to_even`.
-/
import LibcruxIotSha3.Sponge.Opaque

open Aeneas Aeneas.Std Result Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Sponge

open libcrux_iot_sha3.Equivalence

-- Defensive seal re-issue: no proof in this file may unfold either side
-- of Bridge 1.
set_option allowUnsafeReducibility true in
attribute [local irreducible] keccak.keccakf1600 keccak_f.keccak_f

/-! ## Load-bearing bit-level identities (BV form)

Three pure-BitVec identities anchor the byte ↔ interleaved-lane bridge:

1. **`lift_lane_bv_xor`** — `lift_lane_bv` distributes over per-half XOR.
2. **`interleave_bv_lift_eq`** — the impl's 13-stage even/odd-bit deposit
   (computing `Lane2U32.interleave (lo, hi)`'s halves) round-trips
   through `lift_lane_bv` to recover `(hi <<32) ||| lo`, i.e.
   `u64_from_le_bytes (lo.toLEBytes ++ hi.toLEBytes)`.
3. **`deinterleave_bv_lift_eq`** — the dual: deinterleave's two output
   halves equal the LE-byte split of `lift_lane_bv even_bits odd_bits`.

All three are discharged purely by `bv_decide` after the relevant unfold.
These are the load-bearing crux of Plan.lean § 1 lines 222–224 and
274–279. -/

/-- `lift_lane_bv` distributes over per-half XOR.  Pure `bv_decide`. -/
theorem lift_lane_bv_xor (z0 z1 w0 w1 : BitVec 32) :
    lift_lane_bv z0 z1 ^^^ lift_lane_bv w0 w1 =
      lift_lane_bv (z0 ^^^ w0) (z1 ^^^ w1) := by
  unfold lift_lane_bv spread_to_even
  bv_decide

/-- Pure-BitVec model of the impl's `Lane2U32.interleave` body
    (Extraction/Funs.lean:116-163), expressed as a function from
    `(lo, hi) : BitVec 32 × BitVec 32` to the resulting `(even, odd)`
    halves.

    This mirrors the 13-stage bit-deposit (six per parity) applied to
    `lane_u64 := (hi << 32) ||| lo`. -/
def interleave_bv (lo hi : BitVec 32) : BitVec 32 × BitVec 32 :=
  let lane_u64 : BitVec 64 := (hi.zeroExtend 64) <<< 32 ||| lo.zeroExtend 64
  let even_bits := lane_u64 &&& 6148914691236517205#64
  let even_bits := even_bits ^^^ (even_bits >>> 1)
  let even_bits := even_bits &&& 3689348814741910323#64
  let even_bits := even_bits ^^^ (even_bits >>> 2)
  let even_bits := even_bits &&& 1085102592571150095#64
  let even_bits := even_bits ^^^ (even_bits >>> 4)
  let even_bits := even_bits &&& 71777214294589695#64
  let even_bits := even_bits ^^^ (even_bits >>> 8)
  let even_bits := even_bits &&& 281470681808895#64
  let even_bits := even_bits ^^^ (even_bits >>> 16)
  let even_bits := even_bits &&& 4294967295#64
  let odd_bits := (lane_u64 >>> 1) &&& 6148914691236517205#64
  let odd_bits := odd_bits ^^^ (odd_bits >>> 1)
  let odd_bits := odd_bits &&& 3689348814741910323#64
  let odd_bits := odd_bits ^^^ (odd_bits >>> 2)
  let odd_bits := odd_bits &&& 1085102592571150095#64
  let odd_bits := odd_bits ^^^ (odd_bits >>> 4)
  let odd_bits := odd_bits &&& 71777214294589695#64
  let odd_bits := odd_bits ^^^ (odd_bits >>> 8)
  let odd_bits := odd_bits &&& 281470681808895#64
  let odd_bits := odd_bits ^^^ (odd_bits >>> 16)
  let odd_bits := odd_bits &&& 4294967295#64
  (even_bits.truncate 32, odd_bits.truncate 32)

/-- Pure-BitVec model of the impl's `Lane2U32.deinterleave` body
    (Extraction/Funs.lean:3993-4065), expressed as a function from
    `(even, odd) : BitVec 32 × BitVec 32` (the two halves of an
    interleaved lane) to the resulting `(lo, hi)` 32-bit pair that an
    LE-byte split of the lifted u64 would yield. -/
def deinterleave_bv (even_bits odd_bits : BitVec 32) : BitVec 32 × BitVec 32 :=
  let evlo := even_bits &&& 65535#32
  let evlo := evlo ^^^ (evlo <<< 16)
  let evlo := evlo &&& 65535#32
  let evlo := evlo ^^^ (evlo <<< 8)
  let evlo := evlo &&& 16711935#32
  let evlo := evlo ^^^ (evlo <<< 4)
  let evlo := evlo &&& 252645135#32
  let evlo := evlo ^^^ (evlo <<< 2)
  let evlo := evlo &&& 858993459#32
  let evlo := evlo ^^^ (evlo <<< 1)
  let evlo5 := evlo &&& 1431655765#32
  let evhi := even_bits >>> 16
  let evhi := evhi ^^^ (evhi <<< 16)
  let evhi := evhi &&& 65535#32
  let evhi := evhi ^^^ (evhi <<< 8)
  let evhi := evhi &&& 16711935#32
  let evhi := evhi ^^^ (evhi <<< 4)
  let evhi := evhi &&& 252645135#32
  let evhi := evhi ^^^ (evhi <<< 2)
  let evhi := evhi &&& 858993459#32
  let evhi := evhi ^^^ (evhi <<< 1)
  let evhi5 := evhi &&& 1431655765#32
  let odlo := odd_bits &&& 65535#32
  let odlo := odlo ^^^ (odlo <<< 16)
  let odlo := odlo &&& 65535#32
  let odlo := odlo ^^^ (odlo <<< 8)
  let odlo := odlo &&& 16711935#32
  let odlo := odlo ^^^ (odlo <<< 4)
  let odlo := odlo &&& 252645135#32
  let odlo := odlo ^^^ (odlo <<< 2)
  let odlo := odlo &&& 858993459#32
  let odlo := odlo ^^^ (odlo <<< 1)
  let odlo5 := odlo &&& 1431655765#32
  let odhi := odd_bits >>> 16
  let odhi := odhi ^^^ (odhi <<< 16)
  let odhi := odhi &&& 65535#32
  let odhi := odhi ^^^ (odhi <<< 8)
  let odhi := odhi &&& 16711935#32
  let odhi := odhi ^^^ (odhi <<< 4)
  let odhi := odhi &&& 252645135#32
  let odhi := odhi ^^^ (odhi <<< 2)
  let odhi := odhi &&& 858993459#32
  let odhi := odhi ^^^ (odhi <<< 1)
  let odhi5 := odhi &&& 1431655765#32
  let lo_out := evlo5 ||| (odlo5 <<< 1)
  let hi_out := evhi5 ||| (odhi5 <<< 1)
  (lo_out, hi_out)

/-- Load-bearing bit-level bridge: lifting the two halves produced by
    `interleave_bv lo hi` recovers the LE-concatenated 64-bit form
    `(hi << 32) ||| lo`.  Discharged by `bv_decide`. -/
theorem interleave_bv_lift_eq (lo hi : BitVec 32) :
    let (e, o) := interleave_bv lo hi
    lift_lane_bv e o = (hi.zeroExtend 64) <<< 32 ||| lo.zeroExtend 64 := by
  simp only [interleave_bv, lift_lane_bv, spread_to_even]
  bv_decide

/-- Load-bearing bit-level bridge: lifting two interleaved halves equals
    the LE-concatenated form of the deinterleave halves.  Discharged by
    `bv_decide`. -/
theorem deinterleave_bv_lift_eq (even_bits odd_bits : BitVec 32) :
    let (lo, hi) := deinterleave_bv even_bits odd_bits
    (hi.zeroExtend 64) <<< 32 ||| lo.zeroExtend 64 =
      lift_lane_bv even_bits odd_bits := by
  simp only [deinterleave_bv, lift_lane_bv, spread_to_even]
  bv_decide

/-! ## Status: bit-level crux done; Aeneas-Triple lift pending

The three load-bearing identities above are the **pure-BitVec** content
of the byte ↔ interleaved-lane bridge.  Lifting them to Aeneas-`Result`
form (i.e. `@[spec]` Triples over `lane.Lane2U32.interleave` and
`.deinterleave`) requires translating ~30 `lift`/`<<<`/`>>>`/`&&&`/`|||`/
`^^^` steps per operation through `Std.U32`/`Std.U64` Aeneas ops — a
sustained but mechanical pass that has been deferred.

The three `@[spec]` Triples for `load_block`, `store_block`, and
`load_block_full` named in Plan.lean § 1 are **not installed in this
file** — see the campaign's hard-blocker report (Phase 1a, second
attempt) for the precise list of prerequisite Triples still to be
discharged.  The orchestrator should treat this file as Phase 1a's
**partial deliverable**: load-bearing BV identities ready, downstream
Triples pending. -/

end libcrux_iot_sha3.Sponge
