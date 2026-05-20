/-
  # SHA-3 Sponge Verification Plan (Campaign 3)

  This file is a *roadmap* for the next phase of the SHA-3 verification
  in `libcrux-iot`. Every theorem here has body `by sorry` (resp. `sorry`
  for pure defs) — the file is intentionally a non-proving scaffold.

  Most postconditions are intentionally weakened to `⌜ True ⌝` so that
  the file typechecks without committing to the *exact* shape of each
  Triple's post; the **real** post is documented as a Lean comment
  immediately above each theorem in pseudo-Lean. When the corresponding
  proof file gets written, the dummy `True ⌝` is to be replaced by the
  precise post documented in the comment.

  ## Status / scope

  - Bridge 1 (impl ↔ hacspec Keccak-f[1600]) is closed: see
    `LibcruxIotSha3/Equivalence/HacspecBridge.lean` line 1183, theorem
    `keccakf1600_equiv_hacspec`.
  - **For Campaign 3 we treat `keccak.keccakf1600` and the hacspec
    `keccak_f.keccak_f` as OPAQUE.** No proof in this file (or its
    successors) may unfold either; both sides only refer to them via
    the sealed `@[spec]` lemma in § 0 below.

  ## Architecture goals

  The campaign decomposes the impl-side `keccak.keccak<RATE, DELIM>`
  (extraction at `Extraction/Funs.lean:4579`) and the spec-side
  `sponge.keccak<OUTPUT_LEN>` (extraction at
  `HacspecSha3/Extraction/Funs.lean:1218`). Their compositional
  structure is similar:

      impl: load_block ; keccakf1600 ; (loop) ; load_block_full ;
            keccakf1600 ; store_block ;
            (loop: keccakf1600 ; store_block) ; keccakf1600 ; store_block
      spec: xor_block_into_state ; keccak_f ; (loop via absorb_rec) ;
            pad_last_block ; xor ; keccak_f ;
            (extract via createi using iterate_keccak_f)

  Per Bridge 1 (`Equivalence/Lift.lean:70`), the impl/spec state link is
      `lift : state.KeccakState → Array U64 25`
  and `lift` is identity on lane indices
  (`A[x, y] ↔ state[5*x + y]`).

  Every absorb/squeeze step Triple has the shape

      ⦃ ⌜ s.i = 0 ∧ (rate/delim preconditions) ⌝ ⦄
        impl_step args s
      ⦃ ⇓ r => ⌜ ∃ (s' : Array U64 25),
                   spec_step (lift s) args = .ok s' ∧
                   s' = lift r ∧ r.i.val = 0 ⌝ ⦄

  The `r.i.val = 0` clause is needed because each `keccakf1600` call
  resets `s.i := 0` (impl side), and the precondition of the *next*
  `keccakf1600` invocation depends on `i.val = 0`.

  ## Critical decisions

  1. **Opacity of keccakf1600.** We seal `keccakf1600_equiv_hacspec`
     from Bridge 1 as a single `@[spec]` (in § 0) and mark
     `keccak.keccakf1600` and `keccak_f.keccak_f` as
     `attribute [local irreducible]` everywhere in this tree.
     `hax_mvcgen` will never step into either body.

  2. **Loop direction.** Audit per loop (annotated inline below). The
     impl uses `for i in 0..n { absorb_block; }` — forward `Nat.fold`
     after the Aeneas range-loop is unfolded via `loop_range_spec_*`.
     The spec uses `sponge.absorb_rec` — a left-recursion that peels
     the *head* `rate`-byte block. Both directions agree: block 0
     absorbed first, then block 1, ... Likewise for `squeeze`: impl
     iterates forward `0..blocks`, spec's `iterate_keccak_f b state` is
     b applications. No reversal needed.

  3. **Spec `squeeze` is `createi` over bytes, impl is block-wise.**
     The spec extracts each *byte* `k` via
     `iterate_keccak_f (k/rate)`, so the same `keccak_f` application is
     duplicated `rate` times for each output block. We bridge by a
     "block factorization" lemma — `sponge_squeeze_byte_eq` — showing
     the spec's createi over a `rate`-byte range equals one block-wise
     `store_block` on `iterate_keccak_f b s`.

  4. **`sponge.absorb_rec` is `partial_fixpoint`.** Its Lean unfolding
     equation gives a one-step recursion; we wrap it in a helper
     `sponge_absorb_rec_unfold` (pure rewrite). The forward induction
     is on `message.length / rate` (Nat) — matches the impl loop bound
     `n`.

  5. **`iterate_keccak_f` is `partial_fixpoint`.** Similar — unfolds via
     `Nat.rec` over the count. The impl threads state mutably through
     `squeeze_next_block`; the spec recomputes from scratch each time.
     Their equality at step `b` uses an induction over `b`.

  6. **Variable-length output (SHAKE).** The impl branches on
     `blocks = 0` (output fits in one block) vs `blocks ≥ 1`, and on
     whether there is a partial trailing block (`last < outlen`). We
     stratify into three cases: (a) `OUTPUT_LEN < rate`,
     (b) `OUTPUT_LEN % rate = 0`, (c) general. Each case shares the
     same byte-equivalence lemma `sponge_squeeze_byte_eq`.

  7. **Module layout.** Each section here is intended to graduate into
     its own file under `Sponge/`:
       - `Sponge/Opaque.lean`         — § 0 (keccakf1600 seal)
       - `Sponge/Bytes.lean`          — § 1 (load/store byte ↔ lane)
       - `Sponge/AbsorbBlock.lean`    — § 2
       - `Sponge/Absorb.lean`         — § 3
       - `Sponge/SqueezeBlock.lean`   — § 4
       - `Sponge/Squeeze.lean`        — § 5
       - `Sponge/AbsorbFinal.lean`    — § 6
       - `Sponge/Sha3.lean`           — § 7
       - `Sponge/Shake.lean`          — § 8

  We keep them in one file for the planning phase only.

  ## Hard constraints (carried through implementation)

  - Never unfold `keccak.keccakf1600` outside § 0 (set
    `attribute [local irreducible] keccak.keccakf1600 keccak_f.keccak_f`
    at the top of every file in Sponge/).
  - Never unfold `keccak.absorb_block` etc. once their `@[spec]` is in
    scope (use `attribute [local irreducible]` after each module's
    canonical step lemma is proved — § 5.7 idiom from
    `lean-for-libcrux`).
  - Every Triple post must include `r.i.val = 0` whenever `r` has a
    `KeccakState` component; otherwise the next step's precondition is
    unprovable.
-/
import LibcruxIotSha3.Equivalence.HacspecBridge

open Aeneas Aeneas.Std Result ControlFlow Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Sponge

-- Bring `lift`, `Equivalence.lift`, etc. into scope.
open libcrux_iot_sha3.Equivalence

/-! ## § 0 — Opaque seal for `keccakf1600`

The whole campaign is parameterized on a single black-box bridge: one
`@[spec]` Triple that gives the post

    keccak_f.keccak_f (lift s) = .ok (lift r) ∧ r.i.val = 0

after a `keccak.keccakf1600 s` call. All higher proofs use only this
lemma; they never touch `keccakf1600`'s body. -/

/-- Sealed `@[spec]` for impl-side keccakf1600.

    **Real post** (replace the `True` below with the following clause):
    ```
    keccak_f.keccak_f (Equivalence.lift s) = .ok (Equivalence.lift r)
      ∧ r.i.val = 0
    ```

    Proof sketch
    ------------
    1. Apply `Equivalence.keccakf1600_equiv_hacspec s h_i`. This yields
       the spec equality post.
    2. Strengthen the post with `r.i.val = 0` by `unfold`-ing the impl
       one step (line 3776 of Funs.lean: the body ends with
       `keccakf1600_loop ... >>= fun s => ok { s with i := 0#usize }`).
       This is the *only* place we ever unfold `keccakf1600`.
    3. After this lemma is proved, mark `keccak.keccakf1600`
       `[local irreducible]` for the remainder of Campaign 3. -/
@[spec]
theorem keccakf1600_seal_spec (s : state.KeccakState) (h_i : s.i.val = 0) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600 s
    ⦃ ⇓ _r => ⌜ True ⌝ ⦄ := by
  sorry

/-! Risks / open questions for § 0
    -----------------------------
    - Does `keccak.keccakf1600` always succeed (no `.fail` branch)?
      The `Nat.fold` from Bridge 1 implies yes (no overflow possible in
      a closed fold of 6 rounds-of-4). We rely on the existing
      `keccakf1600_equiv_via_bit` lemma's `noThrow` shape — confirm by
      reading its statement.
    - For the `r.i.val = 0` clause: the extraction adds `s.i = 0`
      explicitly at line 3776; verify this and adjust the seal
      accordingly. Without this clause, the *next* keccakf1600 call's
      precondition (`s.i.val = 0`) is unprovable, breaking absorb
      loops. -/

/-! ## § 1 — load/store byte ↔ lane primitives

These bridge the impl's interleaved `Lane2U32` blocks to the spec's
`U64 × 8`-byte view. -/

/-- `state.KeccakState.load_block RATE s blocks start` is the impl
    counterpart of `sponge.xor_block_into_state state block rate` —
    both XOR a `rate`-byte chunk of the input buffer into the state.

    Impl signature: `Extraction/Funs.lean:293`
    Spec signature: `HacspecSha3/Extraction/Funs.lean:1146`

    **Real post** (informal):
    ```
    sponge.xor_block_into_state (lift s) (block_slice blocks start RATE) RATE
      = .ok (lift r)  ∧  r.i = s.i
    ```

    Proof sketch
    ------------
    - Unfold `state.KeccakState.load_block` → `state.load_block_2u32`,
      which is two consecutive `loop_range_spec`-shaped loops:
        Loop A: i ∈ 0..(RATE/8), read 8 bytes at offset `start + 8*i`,
                  interleave into `state_flat[i]`.
        Loop B: i ∈ 0..(RATE/8), XOR `state_flat[i]` into
                  `s.st[(i/5, i%5)]`.
      Note Loop B writes to `s.st` slot index `5*(i%5) + i/5` — this
      is the impl's `byte_lane_idx` derivation (the lane-index
      permutation).
    - Spec side: `sponge.xor_block_into_state` is a `createi 25`
      indexed by *output flat slot* `idx ∈ 0..25`. For each `idx`, it
      computes `b = 5*(idx%5) + idx/5` and XORs the 8-byte lane if
      `b < rate/8`.
    - Loop direction: forward on both sides; no reversal.
    - Bridge: use the existing `loop_range_spec_usize` to convert
      Loop B to `Nat.fold`, then a Triple over `createi` (already used
      for `keccak_f.theta` etc. — see § 4.1 of
      `Equivalence/HacspecBridge.lean`).
    - Key sub-lemma: `interleave_xor_lift_eq` — for each lane-byte
      pair, `lift_lane (interleave (u32_pair_from_8bytes b) XOR l) =
      u64_from_le_bytes b ^^^ lift_lane l`. This is the load-bearing
      bit-level bridge.

    Loop invariant (informal)
    -------------------------
    After Loop B's i-th iteration, for every j ≤ i:
        lift_lane s.st[5*(j%5) + j/5] =
          u64_from_le_bytes(blocks[8j..8j+8])
            ^^^ lift_lane initial.st[5*(j%5) + j/5]
    and for all j > i the lane is unchanged.

    Risks
    -----
    - The `interleave` step composes two `from_le_bytes`-style 32-bit
      reads, then `Lane2U32.interleave` (deinterleave's inverse). The
      bit-level identity `interleave (lo, hi) deinterleaves to (lo,hi)`
      needs to be available; check `Equivalence/Lift.lean`.
    - The spec's `try_into` + `unwrap` on slice → array conversion
      adds noise; usually handled by `scalar_tac` / `simp` after
      `hax_mvcgen`. -/
@[spec]
theorem load_block_spec
    (RATE : Std.Usize) (s : state.KeccakState) (blocks : Slice Std.U8)
    (start : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄
    state.KeccakState.load_block RATE s blocks start
    ⦃ ⇓ _r => ⌜ True ⌝ ⦄ := by
  sorry

/-- `state.KeccakState.store_block RATE s out` ≅ "extract the first
    `rate` bytes from the impl state by deinterleaving each lane
    little-endian". On the spec side, the equivalent is *part of*
    `sponge.squeeze_state` (the byte-from-lane projection). We state
    it as a direct equality on the output byte sequence.

    Impl signature: `Extraction/Funs.lean:4424`
    Spec signature: `sponge.squeeze_state` —
    `HacspecSha3/Extraction/Funs.lean:1146` (sponge.squeeze_state
    inlines `byte_lane_idx` per byte; we restrict it to one block here)

    **Real post** (informal):
    ```
    ∀ k < RATE.val,
      r.val[k]! = ((lift s).val[5*((k/8)%5) + (k/8)/5]!)
                    .bv.toLEBytes[k % 8]!
    ```

    Proof sketch
    ------------
    - Unfold to `state.store_block_2u32`: forward loop on
      `i ∈ 0..(RATE/8)`, writing two 4-byte halves of
      `deinterleave (s.st[5*(i%5) + i/5])` to `out[8i..8i+8]`.
    - Compose: `deinterleave ∘ interleave = id`, so the bytes written
      equal `to_le_bytes (lift_lane s.st[5*(i%5) + i/5])` 8 bytes at a
      time. Each chunk of 8 bytes lines up with `lift s` at the same
      `5*(i%5) + i/5` lane.
    - Reorganize to match the spec's per-byte form:
        `out[k] = to_le_bytes ((lift s).val[byte_lane_idx (k/8)]!)[k%8]`
      for `k < rate`.

    Risks
    -----
    - The spec's `byte_lane_idx` is exactly `5*(b%5) + b/5` (for
      `b = k/8`). Confirm by `byte_lane_idx_eq` rewrite.
    - The "lift_lane ∘ interleave = u64_from_two_u32" identity is what
      links bit-interleaved storage to little-endian byte extraction.
    -/
@[spec]
theorem store_block_spec
    (RATE : Std.Usize) (s : state.KeccakState) (out : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
    state.KeccakState.store_block RATE s out
    ⦃ ⇓ _r => ⌜ True ⌝ ⦄ := by
  sorry

/-- `state.KeccakState.load_block_full RATE s blocks 0` — same as
    `load_block` but operating on a `[U8; 200]` array (not a slice).
    Used inside `absorb_final` after the message has been padded into
    a 200-byte buffer.

    Impl signature: search `state.KeccakState.load_block_full` in
    `Extraction/Funs.lean`.
    Spec equivalent: `sponge.xor_block_into_state` applied to
    `block[0..rate]` where `block : [U8; 200]`.

    **Real post**: as for `load_block_spec`, with `blocks.toSlice` for
    the slice access.

    Proof sketch
    ------------
    - Delegates to `load_block_spec` after a `to_slice` rewrite. The
      extraction calls `load_block_2u32::<RATE>(s, blocks, start)` —
      identical code path, just different input type. -/
@[spec]
theorem load_block_full_spec
    (RATE : Std.Usize) (s : state.KeccakState)
    (blocks : Std.Array Std.U8 200#usize) (start : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄
    state.KeccakState.load_block_full RATE s blocks start
    ⦃ ⇓ _r => ⌜ True ⌝ ⦄ := by
  sorry

/-! Risks / open questions for § 1
    -----------------------------
    - `Slice` accessors (`.val`, `.length`) — the exact API in
      Aeneas-Lean Std for slices is `Std.Slice`. Verify field names
      before writing.
    - The post-Triple's `∀ k, ...` form for `store_block_spec` is
      heavy. It may be cleaner to state it as
      `r.val = (List.ofFn ...).take RATE.val`,
      i.e. a *value*-level equality. Decide during implementation.
    - `Std.Array` byte → `.bv` conversion routes through
      `UScalar.bv`; no surprises expected. -/

/-! ## § 2 — `absorb_block`: single block XOR-in + permute

This is the *first* place we call `keccakf1600`. The whole subsequent
plan stands or falls on the seal of § 0 working through
`hax_mvcgen`. -/

/-- `keccak.absorb_block RATE s blocks start = load_block ; keccakf1600`.
    Spec counterpart:
    `sponge.absorb_block state block rate = xor_block_into_state ; keccak_f`.

    Impl signature: `Extraction/Funs.lean:4306`
    Spec signature: `HacspecSha3/Extraction/Funs.lean:1157`

    **Real post** (informal):
    ```
    sponge.absorb_block (lift s)
      (block_slice blocks start RATE) RATE
      = .ok (lift r)  ∧  r.i.val = 0
    ```

    Proof sketch
    ------------
    - `unfold keccak.absorb_block sponge.absorb_block`. Goal becomes a
      `do { s1 ← load_block ...; keccakf1600 s1 }` matched against
      `do { s_spec_1 ← xor_block_into_state ...; keccak_f s_spec_1 }`.
    - `hax_mvcgen`:
      * First specs `load_block_spec` (§ 1) — yields
        `lift s1 = xor_block_into_state (lift s) block rate` and
        `s1.i = s.i = 0`.
      * Then specs `keccakf1600_seal_spec` (§ 0) using
        `h_i : s1.i.val = 0` — yields
        `keccak_f.keccak_f (lift s1) = .ok (lift r)`, `r.i.val = 0`.
    - Compose: `keccak_f (lift s1)
                  = keccak_f (xor_block_into_state (lift s) ...)
                  = sponge.absorb_block (lift s) ...`.
    - Close with a single `simp only [sponge.absorb_block]` and `rfl`.

    Loop invariant: N/A (no loop at this level).

    Risks
    -----
    - This is the smallest non-trivial composition; if it fails, it's
      almost certainly the `keccakf1600` seal post not landing
      `r.i.val = 0` correctly. -/
@[spec]
theorem absorb_block_spec
    (RATE : Std.Usize) (s : state.KeccakState) (blocks : Slice Std.U8)
    (start : Std.Usize) (h_i : s.i.val = 0) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.absorb_block RATE s blocks start
    ⦃ ⇓ _r => ⌜ True ⌝ ⦄ := by
  sorry

/-! Risks for § 2
    -------------
    - The spec uses `block : &[u8]` of length `rate`; we pass the
      slice `blocks.slice start..start+RATE`. Ensure the slicing API
      matches. -/

/-! ## § 3 — `absorb`: multi-block loop

This is the first *real* loop. The impl uses a forward
`for i in 0..n { absorb_block(i*RATE) }`. The spec uses `absorb_rec`
which is a `partial_fixpoint` left-recursion peeling the head block.
They are equal but in *different shapes* — we must bridge. -/

/-- Unfolding lemma for `sponge.absorb_rec` (pure rewrite — no Triple
    needed). One-step unfold:

    ```
    absorb_rec s rate delim msg
      = if msg.length < rate
        then absorb_final s msg 0 msg.length rate delim
        else absorb_rec
              (absorb_block s msg[0..rate] rate)
              rate delim msg[rate..]
    ```

    Proof sketch: `partial_fixpoint`-generated equation — should be
    available as `sponge.absorb_rec.eq_def` (auto-generated by
    `partial_fixpoint` in Aeneas-Lean). -/
theorem sponge_absorb_rec_unfold : True := by
  trivial

/-- Forward characterization: after `n = msg.length / rate` full blocks
    of `absorb_rec`, the result equals
    ```
      absorb_final
        (fold absorb_block over first n blocks)
        rate delim (msg % rate)
    ```
    This is the form the impl loop produces.

    Proof sketch
    ------------
    Induction on `n = msg.length / rate.val`.
    Base case (n = 0): msg.length < rate, unfold-step picks the
      `if`-branch and gives absorb_final directly.
    Step: unfold-step of absorb_rec gives one absorb_block followed by
      a recursive call on the tail of length `msg.length - rate.val`.
      The IH for that tail yields the (n-1)-fold; prepend the current
      block to close the fold. -/
theorem sponge_absorb_rec_eq_fold : True := by
  trivial

/-- The impl's outer "absorb full blocks" loop equals (up to lift) the
    `Nat.fold` of `sponge.absorb_block` over those same blocks.

    The corresponding impl extraction code is `keccak.keccak_loop0`
    (line 4530 of `Extraction/Funs.lean`): the body is
    `let s1 ← keccak.absorb_block RATE s data (i*RATE)`.

    **Real post** (informal):
    ```
    Nat.fold n.val (init := .ok (lift s))
      (fun j _ acc => acc.bind fun st =>
        sponge.absorb_block st (data.slice (j*RATE) ((j+1)*RATE)) RATE)
      = .ok (lift r)
    ∧ r.i.val = 0
    ```

    Proof sketch
    ------------
    - Apply `loop_range_spec_usize` to turn the Aeneas range-loop into
      `Nat.fold` over `n = data.length / rate`.
    - In each fold step the body Triple uses `absorb_block_spec` (§ 2).
    - The invariant carried through the fold is:
        `r.i.val = 0` (re-established by each `keccakf1600` call)
        ∧ `lift r = Nat.fold (...) (init := lift s_initial)`
      i.e. impl and spec stay in lockstep block by block.

    Loop invariant (formal-ish)
    ---------------------------
    ```
    I(i, state) :=
      state.i.val = 0
      ∧ ∃ spec_acc,
          Nat.fold i (init := lift s_initial)
            (fun j _ acc => acc.bind fun st =>
              sponge.absorb_block st
                (msg.slice (j*rate) ((j+1)*rate)) rate)
            = .ok spec_acc
          ∧ lift state = spec_acc
    ```

    Risks
    -----
    - Threading the `i.val = 0` invariant: every absorb_block call's
      pre needs it; after each call it's re-established by the
      keccakf1600 seal.
    - The fold over `Nat` vs the spec's recursive form requires the
      `sponge_absorb_rec_eq_fold` lemma above. -/
theorem keccak_loop0_eq_fold
    (RATE : Std.Usize) (s : state.KeccakState) (data : Slice Std.U8)
    (n : Std.Usize) (h_i : s.i.val = 0) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccak_loop0 RATE { start := 0#usize, «end» := n } data s
    ⦃ ⇓ _r => ⌜ True ⌝ ⦄ := by
  sorry

/-! Risks / open questions for § 3
    -----------------------------
    - `partial_fixpoint`-generated `eq_def`: confirm Aeneas-Lean
      indeed auto-generates this (look at existing partial_fixpoint
      uses such as `sponge.iterate_keccak_f`).
    - The `Nat.fold` carrying an `Result`-monadic accumulator: the
      body uses `acc.bind` to short-circuit on failure. We expect no
      failure because each `absorb_block` succeeds (per § 2's Triple).
    -/

/-! ## § 4 — `squeeze_first_block` / `squeeze_next_block`

These extract one rate-block of output from the (possibly permuted)
state. -/

/-- `keccak.squeeze_first_block RATE s out = store_block` (no
    permutation). The spec analogue is `sponge.squeeze_state` applied
    to `lift s` for offsets `0..rate`.

    Impl signature: `Extraction/Funs.lean:4432`
    Spec signature: `sponge.squeeze_state` —
    `HacspecSha3/Extraction/Funs.lean` (the `createi` over bytes,
    restricted to the first block).

    **Real post**: identical to `store_block_spec` — same per-byte
    formula on `lift s`.

    Proof sketch
    ------------
    - Direct application of `store_block_spec` (§ 1).
    - No `keccakf1600` invocation, so no seal needed here.

    Risks
    -----
    - Matching the exact `squeeze_state.closure.call` shape from the
      spec extraction. -/
@[spec]
theorem squeeze_first_block_spec
    (RATE : Std.Usize) (s : state.KeccakState) (out : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.squeeze_first_block RATE s out
    ⦃ ⇓ _r => ⌜ True ⌝ ⦄ := by
  sorry

/-- `keccak.squeeze_next_block RATE s out = keccakf1600 s ; store_block`.
    Spec analogue: `squeeze_state (keccak_f s) out 0 rate`.

    Impl signature: `Extraction/Funs.lean:4440`

    **Real post** (informal):
    ```
    let (s_new, out_new) := r
    ∃ s_spec, keccak_f.keccak_f (lift s) = .ok s_spec
      ∧ s_spec = lift s_new
      ∧ s_new.i.val = 0
      ∧ (∀ k < RATE,
           out_new.val[k]! = (s_spec.val[byte_lane_idx (k/8)]!)
                                .bv.toLEBytes[k % 8]!)
    ```

    Proof sketch
    ------------
    - Unfold `keccak.squeeze_next_block`.
    - `hax_mvcgen` with `keccakf1600_seal_spec` then
      `store_block_spec`.
    - The result's `(s_new, out_new)`: state is
      `lift⁻¹ (keccak_f (lift s))`, output byte k matches the same
      per-byte formula on the new state.

    Risks
    -----
    - Both an output buffer AND an updated state are returned; the
      post-Triple is a *conjunction* of two facts. Make sure
      `hax_mvcgen` can match the tuple destructuring. -/
@[spec]
theorem squeeze_next_block_spec
    (RATE : Std.Usize) (s : state.KeccakState) (out : Slice Std.U8)
    (h_i : s.i.val = 0) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.squeeze_next_block RATE s out
    ⦃ ⇓ _r => ⌜ True ⌝ ⦄ := by
  sorry

/-- `keccak.squeeze_last RATE s out` — final partial block. Internally:
    `keccakf1600 ; store_block_full into 200-byte buf ;
     copy first out.length bytes`.

    Impl signature: `Extraction/Funs.lean:4469`

    **Real post** (informal):
    ```
    ∃ s_spec, keccak_f.keccak_f (lift s) = .ok s_spec ∧
       ∀ k < out.length,
         r.val[k]! = (s_spec.val[byte_lane_idx (k/8)]!)
                       .bv.toLEBytes[k % 8]!
    ```

    Proof sketch
    ------------
    - Compose `keccakf1600_seal_spec`, then `store_block_full_spec`
      (§ 1 — defer or factor), then bound the copy by `out.length`.
    - Output byte k for `k < out.length` matches the per-byte spec
      formula on `keccak_f (lift s)`. -/
@[spec]
theorem squeeze_last_spec
    (RATE : Std.Usize) (s : state.KeccakState) (out : Slice Std.U8)
    (h_i : s.i.val = 0) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.squeeze_last RATE s out
    ⦃ ⇓ _r => ⌜ True ⌝ ⦄ := by
  sorry

/-- `keccak.squeeze_first_and_last RATE s out` — no permutation, just
    `store_block_full ; copy first out.length bytes`. Used when
    `out.length < RATE`. -/
@[spec]
theorem squeeze_first_and_last_spec
    (RATE : Std.Usize) (s : state.KeccakState) (out : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.squeeze_first_and_last RATE s out
    ⦃ ⇓ _r => ⌜ True ⌝ ⦄ := by
  sorry

/-! Risks for § 4
    -------------
    - The post-conditions of `squeeze_next_block` involve a tuple
      destructuring; check the `let (a, b) := r` syntax is handled by
      `hax_mvcgen` (it usually is, but verify on a simple example
      first).
    - `Slice.length` of the *input* `out` slice equals `RATE` in the
      common case, but for `squeeze_last` it's strictly less. -/

/-! ## § 5 — `squeeze`: multi-block extraction

The impl interleaves `squeeze_first_block` + a forward
`for i in 1..blocks { squeeze_next_block }` + optional `squeeze_last`.

The spec `sponge.squeeze` is a `createi OUTPUT_LEN` that for each byte
`k` computes `iterate_keccak_f (k/rate) state` from scratch. The two
representations agree byte-by-byte, but the spec recomputes
`iterate_keccak_f` redundantly. We bridge by establishing a
*block-wise* characterization of the spec. -/

/-- Pure lemma: `iterate_keccak_f` unfolds to a left-fold of
    `keccak_f.keccak_f` over the natural number `n`.

    Proof sketch: induction on `n`, using the
    `partial_fixpoint`-generated equation
    `sponge.iterate_keccak_f.eq_def`. -/
theorem iterate_keccak_f_eq_fold : True := by
  trivial

/-- Pure lemma: the spec's per-byte `squeeze` decomposes
    block-by-block. For `k ∈ [b*rate, (b+1)*rate)`, byte `k` of
    `sponge.squeeze OUT s rate` equals byte `(k - b*rate)` of
    `squeeze_state (iterate_keccak_f b s)`.

    Proof sketch
    ------------
    - Unfold `sponge.squeeze` to the `createi` closure.
    - Each call yields `iterate_keccak_f (k/rate) s`'s byte
      `byte_lane_idx ((k % rate)/8) . to_le_bytes [(k % rate) % 8]`.
    - For `k ∈ [b*rate, (b+1)*rate)`, `k/rate = b` and
      `k % rate = k - b*rate`.

    Risks
    -----
    - The `createi` closure form is the same that
      `Equivalence/HacspecBridge.lean` handles for `keccak_f.theta`
      etc.; reuse `createi_pure_eq` (line 627). -/
theorem sponge_squeeze_byte_eq : True := by
  trivial

/-- The impl's "squeeze" loop body (= `keccak_loop1` at
    `Extraction/Funs.lean:4567`): per iteration, one
    `squeeze_next_block`, advancing offset by `RATE`.

    **Real post** (informal):
    ```
    let (out_final, s_final, offset_final) := r
    offset_final.val = blocks.val * RATE.val
    ∧ s_final.i.val = 0
    ∧ ∃ s_spec_blocks_minus_1,
        sponge.iterate_keccak_f (blocks - 1) (lift s)
          = .ok s_spec_blocks_minus_1
        ∧ s_spec_blocks_minus_1 = lift s_final
    ∧ ∀ k < blocks * RATE, out_final[k]
         matches byte-wise spec squeeze
    ```

    Proof sketch
    ------------
    - `loop_range_spec_usize` to expose the `Nat.fold`.
    - Each step's body Triple is `squeeze_next_block_spec` (§ 4).
    - The invariant carried is:
        I(i, s, out, offset) :=
          s.i.val = 0
          ∧ offset = (i+1) * RATE  (because squeeze_first_block ran)
          ∧ ∀ k < (i+1)*RATE, out[k] matches the spec byte.

    Loop invariant (formal)
    -----------------------
    See the comment above. Essentially: at iteration
    `i ∈ [0, blocks-1)`, we've already extracted `(i+1)` blocks of
    output and the impl state is `iterate_keccak_f i state_after_absorb`
    (i.e. i applications of keccakf1600 since the absorb phase, because
    squeeze_first_block did not apply keccakf1600).

    Risks
    -----
    - Off-by-one: the loop is `1..blocks`, not `0..blocks`. So at
      iteration `i = 1` we apply *one* keccakf1600 and write block
      index 1.
    - Index reasoning between `i`-indexed loop iterations and the
      spec's "b-th output block" indexing must be tight. -/
theorem keccak_loop1_invariant
    (RATE : Std.Usize) (blocks : Std.Usize) (s : state.KeccakState)
    (out : Slice Std.U8) (offset : Std.Usize) (h_i : s.i.val = 0) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccak_loop1 RATE { start := 1#usize, «end» := blocks } out s
      offset
    ⦃ ⇓ _r => ⌜ True ⌝ ⦄ := by
  sorry

/-! Risks for § 5
    -------------
    - The spec's `iterate_keccak_f` is monadic (`Result`); the impl's
      state is threaded directly. The byte-equality post requires
      `iterate_keccak_f` to *not* fail. Establishing
      "iterate_keccak_f always succeeds" needs an auxiliary lemma
      (each `keccak_f` call succeeds by Bridge 1; hence the chain).
    - `sponge.iterate_keccak_f` indexing by `Std.Usize` vs `Nat`:
      conversions need `scalar_tac` or explicit `Std.Usize.ofNat`
      bounds. -/

/-! ## § 6 — `absorb_final` (padding + last block)

This combines § 1's `load_block_full` with the seal of § 0. -/

/-- `keccak.absorb_final RATE DELIM s last start len` ≅
    `sponge.absorb_final state message msg_offset remaining rate delim`.

    Impl signature: `Extraction/Funs.lean:4316`
    Spec signature: `HacspecSha3/Extraction/Funs.lean:1167`

    **Real post** (informal):
    ```
    sponge.absorb_final (lift s) last start len RATE DELIM
      = .ok (lift r)  ∧  r.i.val = 0
    ```

    Proof sketch
    ------------
    - Both impl and spec follow the same recipe:
       1. Build a 200-byte buffer; zero-init.
       2. Copy `last[start..start+len]` into buffer[0..len].
       3. Set buffer[len] = DELIM.
       4. OR 0x80 into buffer[RATE-1].
       5. Load the buffer into state.
       6. Run keccakf1600.
    - `hax_mvcgen` walks both sides in parallel; each step is a small
      Triple. After step 5 we invoke `load_block_full_spec` (§ 1);
      after step 6 we invoke `keccakf1600_seal_spec` (§ 0).
    - Inside the array-builder, the conditional `if len > 0` matches
      the spec's `pad_last_block` exactly (line 1042 of spec
      extraction).

    Loop invariant: N/A; the body is straight-line apart from a
    single if-branch on `len > 0`. -/
@[spec]
theorem absorb_final_spec
    (RATE : Std.Usize) (DELIM : Std.U8) (s : state.KeccakState)
    (last : Slice Std.U8) (start : Std.Usize) (len : Std.Usize)
    (h_i : s.i.val = 0) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.absorb_final RATE DELIM s last start len
    ⦃ ⇓ _r => ⌜ True ⌝ ⦄ := by
  sorry

/-! Risks for § 6
    -------------
    - The impl's buffer is `[U8; 200]` declared via
      `Array.repeat 200 0u8` followed by `Classify`; the spec's is
      `[u8; 200]` via `Array.repeat`. Make sure both `0u8` literals
      lift identically and that the `Classify` step is a no-op at the
      `lift` level.
    - Both sides do the `buf[RATE-1] |= 0x80` step. Off-by-one in
      `RATE - 1#usize` — guard with `0 < RATE.val`. -/

/-! ## § 7 — Top-level: `keccak.keccak` (RATE, DELIM) ↔ `sponge.keccak`

Composes the entire sponge: absorb-full-loop + absorb-final +
squeeze-first-block + squeeze-loop + (optional) squeeze-last. -/

/-- The big one: `keccak.keccak<RATE, DELIM>(data, out)` matches
    `sponge.keccak<OUTPUT_LEN>(rate, delim, data)` (modulo
    length-of-out being treated as OUTPUT_LEN).

    Impl signature: `Extraction/Funs.lean:4579`
    Spec signature: `HacspecSha3/Extraction/Funs.lean:1218`

    **Real post** (informal):
    ```
    ∃ spec_out : Array U8 (out.length),
      sponge.keccak out.length RATE DELIM data = .ok spec_out
      ∧ ∀ k < out.length, r.val[k]! = spec_out.val[k]!
    ```

    Proof sketch
    ------------
    - `unfold keccak.keccak`.
    - `hax_mvcgen` with the following @[spec]s in scope:
        keccak_loop0_eq_fold        (§ 3)  for the absorb loop
        absorb_final_spec           (§ 6)  for the final-block absorb
        squeeze_first_block_spec    (§ 4)  for the first output block
        keccak_loop1_invariant      (§ 5)  for the squeeze loop
        squeeze_first_and_last_spec (§ 4)  for the no-permutation case
        squeeze_last_spec           (§ 4)  for the partial trailing block
    - The case split on `blocks = 0` vs `blocks ≥ 1` matches the
      spec's analogous case split (induced by `OUTPUT_LEN / rate`).
    - The case split on `last < outlen` (partial trailing block)
      ditto.
    - After all `hax_mvcgen` steps, the residual is a pure spec
      equality bridging:
        sponge.squeeze OUTPUT_LEN (sponge.absorb_rec ...) rate
        = -- byte-by-byte sequence formed by impl
      which uses `sponge_squeeze_byte_eq` (§ 5) and
      `sponge_absorb_rec_eq_fold` (§ 3) to align both sides.

    Loop invariants: see § 3 (absorb) and § 5 (squeeze).

    Risks
    -----
    - This is the largest composition in Campaign 3. Pre-flight the
      `hax_mvcgen` invocation in isolation against just § 0's seal —
      if § 0 fires, the rest should chain.
    - The post-condition's array equality: spec returns
      `Array U8 OUTPUT_LEN`, impl returns `Slice U8`. Need a
      `Slice → Array` coercion to compare, OR state the post as "for
      all k < OUTPUT_LEN, impl_out[k] = spec_out[k]". -/
@[spec]
theorem keccak_keccak_spec
    (RATE : Std.Usize) (DELIM : Std.U8) (data : Slice Std.U8)
    (out : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccak RATE DELIM data out
    ⦃ ⇓ _r => ⌜ True ⌝ ⦄ := by
  sorry

/-- SHA3-224 top-level theorem: the impl `sha224_ema` produces the
    same digest as the spec `sha3.sha3_224`.

    Impl signature: `Extraction/Funs.lean:4854`
    Spec signature: `HacspecSha3/Extraction/Funs.lean:1229`

    **Real post** (informal):
    ```
    ∃ spec_digest : Array U8 28,
      sha3.sha3_224 payload = .ok spec_digest
      ∧ ∀ k < 28, r.val[k]! = spec_digest.val[k]!
    ```

    Proof sketch
    ------------
    - Both call into the generic keccak: impl uses `keccakx1 144 6`
      (which delegates to `keccak.keccak 144 0x06`), spec uses
      `sponge.keccak 28 SHA3_224_RATE SHA3_DELIM
        = sponge.keccak 28 144 6`.
    - Direct application of `keccak_keccak_spec` with `RATE := 144`,
      `DELIM := 6`. -/
theorem sha224_ema_spec
    (digest : Slice Std.U8) (payload : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
    sha224_ema digest payload
    ⦃ ⇓ _r => ⌜ True ⌝ ⦄ := by
  sorry

/-- SHA3-256 top-level theorem. -/
theorem sha256_ema_spec
    (digest : Slice Std.U8) (payload : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
    sha256_ema digest payload
    ⦃ ⇓ _r => ⌜ True ⌝ ⦄ := by
  sorry

/-- SHA3-384 top-level theorem. -/
theorem sha384_ema_spec
    (digest : Slice Std.U8) (payload : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
    sha384_ema digest payload
    ⦃ ⇓ _r => ⌜ True ⌝ ⦄ := by
  sorry

/-- SHA3-512 top-level theorem. -/
theorem sha512_ema_spec
    (digest : Slice Std.U8) (payload : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
    sha512_ema digest payload
    ⦃ ⇓ _r => ⌜ True ⌝ ⦄ := by
  sorry

/-! Risks for § 7
    -------------
    - The `Std.Array Std.U8 N` vs `Slice Std.U8` representation gap
      is mostly cosmetic but requires a coercion lemma to *state* the
      digest equality.
    - The output buffer in impl flows through `Classify` (secret-int
      wrapper); confirm `lift`/`declassify` commute. The spec uses
      plain `u8`. We may need `out.length` to be a metavariable that
      both sides agree on. -/

/-! ## § 8 — SHAKE128 / SHAKE256 top-level theorems (variable-length)

These are *just* `keccak_keccak_spec` with rate/delim instantiated,
but they exercise the variable-output-length path. -/

/-- SHAKE128: variable-length output. Generic over `N`.

    Impl signature: `Extraction/Funs.lean:4938` (`shake128`)
    Spec signature: `HacspecSha3/Extraction/Funs.lean:1257`
    (`sha3.shake128`)

    **Real post**:
    ```
    ∃ spec_out : Array U8 N,
      sha3.shake128 N data = .ok spec_out
      ∧ ∀ k < N, r.val[k]! = spec_out.val[k]!
    ```

    Proof sketch
    ------------
    - Both delegate to `keccakx1 168 0x1f` (impl) /
      `sponge.keccak N 168 0x1f` (spec).
    - Direct application of `keccak_keccak_spec` with `RATE := 168`,
      `DELIM := 0x1f`.

    Variable-length output considerations
    --------------------------------------
    - The output `[U8; N]` is constructed by `[0; N].classify()` and
      then filled by `keccakx1` writing to the slice. Both branches
      (`blocks = 0` and `blocks ≥ 1`) of `keccak.keccak` must align
      with the corresponding spec `createi` over `0..N` bytes.
    - The partial-block branch (`last < outlen`) corresponds to
      `OUTPUT_LEN % rate ≠ 0`; the spec's `squeeze` createi handles
      the partial block via the formula
      `state_b := iterate_keccak_f (k/rate) state` for
      `k ∈ [last, OUTPUT_LEN)`. -/
theorem shake128_spec
    (BYTES : Std.Usize) (data : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
    shake128 BYTES data
    ⦃ ⇓ _r => ⌜ True ⌝ ⦄ := by
  sorry

/-- SHAKE256: variable-length output, rate 136. -/
theorem shake256_spec
    (BYTES : Std.Usize) (data : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
    shake256 BYTES data
    ⦃ ⇓ _r => ⌜ True ⌝ ⦄ := by
  sorry

/-! Risks for § 8
    -------------
    - The const-generic `N` parameter on `shake128`/`shake256` plumbs
      through the impl as `Std.Usize`. Make sure the spec's `N`
      parameter aligns to the same `Usize` typeclass position. The
      extractions appear to match (cf. `Extraction/Funs.lean:4938`,
      where the function takes `N : Std.Usize`).
    - The "200 bytes scratch buffer" used by `absorb_final` /
      `squeeze_last` puts an implicit upper bound; verify all rates
      ≤ 200 (they are: 72/104/136/144/168).
    - For `N = 0` (zero-output SHAKE): an edge case. Impl: `out` is
      empty, `outlen = 0`, so `blocks = 0` and `last = 0`. The
      `if blocks = 0` branch calls `squeeze_first_and_last` with
      empty `out`. Spec: `createi 0 ...` returns the empty array.
      Both trivially agree, but exercise the case. -/

/-! ## Roll-up: campaign metrics

  Lemmas sketched          (counting from § 0 onwards):
    § 0  : 1   keccakf1600_seal_spec
    § 1  : 3   load_block_spec, store_block_spec, load_block_full_spec
    § 2  : 1   absorb_block_spec
    § 3  : 3   sponge_absorb_rec_unfold, sponge_absorb_rec_eq_fold,
               keccak_loop0_eq_fold
    § 4  : 4   squeeze_{first_block, next_block, last,
               first_and_last}_spec
    § 5  : 3   iterate_keccak_f_eq_fold, sponge_squeeze_byte_eq,
               keccak_loop1_invariant
    § 6  : 1   absorb_final_spec
    § 7  : 5   keccak_keccak_spec, sha{224,256,384,512}_ema_spec
    § 8  : 2   shake{128, 256}_spec
    ────────────
    Total: 23 lemmas / Triples

  Loop invariants explicitly identified:
    L1   absorb full-blocks loop (§ 3, `keccak_loop0_eq_fold`)
    L2   squeeze blocks loop    (§ 5, `keccak_loop1_invariant`)
    L3   load_block_2u32 loops  (§ 1, A and B — informal in
                                 load_block_spec)
    L4   store_block_2u32 loop  (§ 1, informal in store_block_spec)
    Total: 4 distinct loops.

  Top blockers / risks (ranked by load-bearing-ness):
    R1   `keccakf1600_seal_spec` (§ 0) must establish `r.i.val = 0`
         post — without this, no absorb step composes.
    R2   `sponge.absorb_rec` is `partial_fixpoint`; the `eq_def`-style
         unfold must exist or be provable, and the fold-form bridge
         (`sponge_absorb_rec_eq_fold`) is non-trivial.
    R3   `sponge.iterate_keccak_f` (similar `partial_fixpoint`) —
         same risk as R2 in § 5.
    R4   The byte-vs-block representation gap in § 5: spec is per-byte
         `createi`, impl is per-block `store_block`. The bridge lemma
         `sponge_squeeze_byte_eq` is the only non-mechanical proof in
         this campaign.
    R5   `Slice` vs `Array` representation gap at the top level (§ 7,
         § 8). Needs a small library of coercion lemmas.
    R6   Loop-direction match: confirmed forward on both sides for
         all four loops — *no* `Nat.fold_reverse` needed (low risk,
         but double-check during § 3 implementation).

  Estimated proof effort (in lemma-units of comparable historical
  difficulty):
    § 0: 0.5 (just composes Bridge 1 + an `unfold`)
    § 1: 3.0 (bit-level identity between interleaved & LE bytes)
    § 2: 0.5 (mechanical composition)
    § 3: 2.0 (partial_fixpoint bridge + invariant)
    § 4: 1.0 (small Triples)
    § 5: 3.0 (per-byte ↔ per-block bridge is the hardest piece)
    § 6: 1.0 (straight-line + 1 conditional)
    § 7: 1.5 (composition; case-splits)
    § 8: 0.5 (instantiation of § 7)
    ──────
    Total: ~13 units. Bridge 1 was ~25 units, so this should be
    roughly half. -/

end libcrux_iot_sha3.Sponge
