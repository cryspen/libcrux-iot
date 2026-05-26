/-
  # Byte ↔ Lane primitives (`load_block`, `store_block`,
  # `load_block_full`).

  This file hosts the three top-level `@[spec]` Triples bridging the
  impl's byte-loop loaders/stores to the sponge spec's byte ↔ lane
  view:

  - `state.KeccakState.load_block_spec`      — unwraps `load_block_2u32`,
    composes the two outer-loop Triples from `Sponge/LoopSpecs.lean`.
  - `state.KeccakState.store_block_spec`     — unwraps `store_block_2u32`,
    composes the outer-loop Triple from `Sponge/LoopSpecs.lean` and
    preserves output-slice length.
  - `state.KeccakState.load_block_full_spec` — delegates to
    `load_block_spec` after `Array.to_slice` coercion.

  ## Post strength (after 2026-05-21 strengthening pass — Partial-B)

  The three Triples here carry the **`i`-preservation** clause needed
  by the absorb/squeeze chaining (`r.i.val = 0` precondition on
  the next `keccakf1600` call). Specifically:

  - `load_block_spec`: `⌜ r.i = s.i ⌝` (loop1 invariant carries it).
  - `store_block_spec`: `⌜ r.val.length = out.val.length ⌝` (returns a
     `Slice U8`, no state component).
  - `load_block_full_spec`: `⌜ r.i = s.i ⌝` (delegates to `load_block`).

  ## Closer report (2026-05-21, extended)

  - **Task 1 (`xor_block_into_state_closure_call_mut_spec`) — LANDED**
    in `Sponge/XorBlockSpec.lean`. The per-cell `@[spec]` for the
    25-cell `from_fn` body drives the inner do-chain (div/rem →
    mul/add → div → if → slice-index → try_from → unwrap → from_le_bytes
    → lift | index_usize). The `b < rate/8` branch matches the
    constructed 8-byte array's `.val` with `list_8_at block.val (8b)`
    via `list_8_at_val_eq_slice`. Axioms: propext, Classical.choice,
    Quot.sound. **This unlocks the absorb_block spec-side composition.**

  - **`sponge_xor_block_into_state_spec` — LANDED** in
    `Sponge/XorBlockSpec.lean`. The direct per-cell post for
    `sponge.xor_block_into_state`, composing `from_fn_pure_spec` with
    Task 1. For each `i < 25`, the output cell equals
    `xor_block_value_at state block rate i`. Axioms: propext,
    Classical.choice, Quot.sound.

  - **Helper defs for loop invariants — LANDED (2026-05-21)** in
    `Sponge/LoopSpecs.lean`:
      * `Lane2U32_from_4byte_LE_pairs blocks start j` — fold-form
        value of `state_flat[j]` *before* the `interleave` step in
        Loop0's body. Two 4-byte LE U32 reads paired into a
        `Lane2U32`.
      * `loop1_lane_at s state_flat j` — fold-form `BitVec 64` value
        produced at impl-flat-index `5*(j%5) + j/5` by Loop1's
        per-iteration XOR (`lift_lane_bv` of the XOR'd halves).
      * `store_block_byte_at s b` — fold-form `U8` at byte index `b`
        of the store loop's output (`lift_lane`-derived LE byte
        split).
    These are the SKILL §8.2-compliant named values used by the
    strengthened invariants. The invariants themselves are still
    deferred (see below).

  - **Tasks 2-4 (loop strong invariants) — DEFERRED.** The current
    weak invariants (`True` / `r.i = s.i` / length-preservation) are
    closed by mvcgen + `scalar_tac`/witness-exhibition tactics that
    do **not** carry through any content-bearing fact about
    `state_flat[j]` / `s'.st[5*(j%5)+j/5]` / `out'[8j+b]`. Strengthening
    each invariant requires re-driving the body mvcgen with new VCs
    that close via `Array.update`/`set_lane`/`setSlice!` characterizations
    plus the BV bridges (`interleave_bv_lift_eq`, `lift_lane_bv_xor`,
    `deinterleave_bv_lift_eq`). Estimated 200-400 lines per loop.
    Helper defs (above) are in place; the remaining work is the
    body-VC closer for each loop.

    **Precise blocker (2026-05-21):** After strengthening Loop1's `inv`
    to `inv k acc := acc.i = s.i ∧ (∀ j ≥ k.val, j < 25 →
    acc.st.val[5*(j%5)+j/5]! = s.st.val[5*(j%5)+j/5]!) ∧ ...`, the body's
    inv-preservation VC for the *untouched-lane* clause becomes
    `(Array.update acc.st (5*(k%5)+k/5) lu1).val[5*(j%5)+j/5]! =
       acc.st.val[5*(j%5)+j/5]!` for `j > k`. This requires
    `List.getElem!_set!_ne` plus an *involution-injectivity* lemma:
    `j ↦ 5*(j%5)+j/5` is injective on `{0,...,24}`. The injectivity
    is closed by `decide` (it's a finite check). The same pattern
    applies to Loop0 (`Array.update state_flat k lu1`) and to Store
    (`(out.setSlice! _ _).setSlice! _ _`). Each loop body requires
    ~200-300 lines of `scalar_tac` + targeted rewriting at each
    branching VC. **Total remaining effort:** ~900-1200 lines across
    LoopSpecs.lean and Bytes.lean.

  - **Tasks 5-7 (textbook posts here) — DEFERRED.** Each chains on
    Tasks 2-4 via a monadic-in-post shape that connects impl-side
    `r.st[5*(j%5) + j/5].bv = s.st[...].bv ^^^ lift_lane_bv (u32_le b1)
    (u32_le b2)` (from strong Loop1) with the spec's
    `xor_block_value_at` via `interleave_bv_lift_eq`. The current
    weak posts are nonetheless sufficient for downstream chaining
    (which only needs termination + `r.i = s.i`).

  Inputs to the strengthening pass:

  - **Loop1** (`state.load_block_2u32_loop1_spec`) now uses the
    invariant `inv k s' := s'.i = s.i`, which is preserved unconditionally
    by the body (the body's only `state.KeccakState` update is
    `set_lane`, which is `{ self with st := a }`).
  - Loop0 (`state.load_block_2u32_loop0_spec`) is unchanged
    (`inv _ _ := True`): loop0 operates on `state_flat`, never touching
    `s`, so `r.i = s.i` for the chain only requires Loop1's invariant.

  ## Remaining post strength (deferred — full "textbook" form)

  The full posts targeted by Plan.lean § 1 lines 244–324 also include:

  - `load_block_spec` (monadic-in-post form):
    `⦃ True ⦄ sponge.xor_block_into_state (lift s) block RATE
       ⦃ ⇓ s' => s' = lift r ⦄`
  - `store_block_spec`:
    `∀ k < RATE.val, r.val[k]! =
       ((Foundation.lift s).val[5*((k/8)%5) + (k/8)/5]!).bv.toLEBytes[k%8]!`
  - `load_block_full_spec`: identical to `load_block_spec` after the
    `Array.to_slice` coercion.

  These require:

  1. Strengthening Loop0's invariant to characterize `state_flat[k]`
     as `interleave_bv (u32_le b1) (u32_le b2)` for each iterated `k`.
  2. Strengthening Loop1's invariant to characterize each touched
     `s'.st[5*(j%5) + j/5]` via `lift_lane_bv_xor`.
  3. Driving `from_fn_pure_spec` (from `Sponge/XorBlockSpec.lean`, the
     `FnMut`-direct analog of `createi_pure_spec`) on
     `sponge.xor_block_into_state`'s closure, which has an `if b < rate/8`
     branch. The conditional lives inside the per-cell `f`-function
     `xor_block_value_at` (also in `XorBlockSpec.lean`), so the closure
     itself is pure (both branches return `(value, c)` with `c`
     unchanged). The per-cell `@[spec]`
     (`xor_block_closure_call_mut_spec`) is staged in
     `XorBlockSpec.lean` — its body needs the inner do-chain
     `slice-index → try_from → unwrap → from_le_bytes → ok` driven
     for the `b < rate/8` branch.

  The current Triples close the *control-flow* gap and pass through
  the `r.i = s.i` invariant needed for the next-`keccakf1600`'s
  precondition. Downstream proofs can now compose against them via `hax_mvcgen`
  to drive the absorb/squeeze loops at the impl side. The remaining
  spec-equation half is deferred to a follow-up pass once the loop-0
  /loop-1 strong invariants land. The closer (2026-05-21) landed
  `from_fn_pure_spec` as new generic infrastructure (it parallels
  `createi_pure_spec` from `HacspecBridge.lean` but takes a `FnMut`
  instance directly).

  The BV-pure identity layer (`interleave_bv`, `deinterleave_bv`,
  `lift_lane_bv_xor`, `interleave_bv_lift_eq`,
  `deinterleave_bv_lift_eq`) now lives in `Sponge/Interleave.lean`'s
  header section — moved there in this commit to break the import cycle
  (`Bytes` would otherwise need `LoopSpecs`, which imports `Interleave`,
  which used to import `Bytes`).

  ## See also

  - `LibcruxIotSha3/Sponge/Plan.lean` § 1 — full Plan with textbook
    posts targeting the strengthened version.
  - `LibcruxIotSha3/Sponge/Opaque.lean` — opaque seal of `keccakf1600`.
  - `LibcruxIotSha3/Sponge/LoopSpecs.lean` — outer-loop Triples
    consumed below.
  - `LibcruxIotSha3/Sponge/SliceSpecs.lean` — slice/byte primitives.
  - `LibcruxIotSha3/Sponge/Interleave.lean` — interleave/deinterleave
    Triples and BV-pure identity layer.
-/
import LibcruxIotSha3.Sponge.LoopSpecs
import LibcruxIotSha3.Sponge.XorBlockSpec

open Aeneas Aeneas.Std Result ControlFlow Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Sponge

open libcrux_iot_sha3.Foundation

-- Defensive seal re-issue: no proof in this file may unfold either side
-- of Bridge 1.
set_option allowUnsafeReducibility true in
attribute [local irreducible] keccak.keccakf1600 keccak_f.keccak_f

/-! ## Top-level Triples for `load_block` / `store_block` /
       `load_block_full`. -/

/-- Local copy of `triple_of_ok_local`: an `.ok v` `Result` satisfies any
    Triple whose post `P r` holds at `v`. -/
private theorem triple_of_ok_bytes {α : Type} {x : Result α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, hp]

/-- Local existence extractor: a Triple yields `∃ v, x = .ok v ∧ P v`. -/
private theorem triple_exists_ok_bytes {α : Type} {x : Result α}
    {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v =>
      refine ⟨v, rfl, ?_⟩
      have := h; simp [Std.Do.Triple, WP.wp] at this; exact this
  | .fail _ =>
      exfalso; have := h; simp [Std.Do.Triple, WP.wp] at this
  | .div =>
      exfalso; have := h; simp [Std.Do.Triple, WP.wp] at this

/-! ### Pure-side reductions for the body of `state.load_block_2u32`.

We capture each step's `.ok`-equation as a small local lemma so the
final assembly is a straight `rw` chain. -/

/-- `core_models.slice.Slice.len v = .ok (Std.Slice.len v)`. -/
private theorem core_slice_len_eq_ok {T : Type} (v : Slice T) :
    core_models.slice.Slice.len v = .ok (Std.Slice.len v) := by
  unfold core_models.slice.Slice.len; rfl

/-- `RATE % 8#usize = .ok 0#usize` whenever `RATE.val % 8 = 0`. -/
private theorem rate_mod_8_eq_ok (RATE : Std.Usize) (h : RATE.val % 8 = 0) :
    (RATE % 8#usize : Result Std.Usize) = .ok 0#usize := by
  -- Use the bv-spec from Aeneas.
  have hnz : ((8#usize : Std.Usize).val : Nat) ≠ 0 := by decide
  -- `UScalar.rem` is `if y.val != 0 then ok ⟨BitVec.umod ...⟩ else fail`.
  show Std.UScalar.rem RATE 8#usize = _
  unfold Std.UScalar.rem
  have hne : ¬ ((8#usize : Std.Usize).val = 0) := hnz
  simp only [bne_iff_ne, ne_eq, hne, not_false_eq_true, ↓reduceIte]
  apply congrArg
  apply Std.UScalar.eq_of_val_eq
  show (BitVec.umod RATE.bv (8#usize : Std.Usize).bv).toNat = (0#usize : Std.Usize).val
  -- Reduce via val/bv toNat. `BitVec.umod x y = x % y` definitionally.
  show RATE.bv.toNat % ((8#usize : Std.Usize).bv).toNat = 0
  have h8 : ((8#usize : Std.Usize).bv).toNat = 8 := by decide
  rw [h8]
  exact h

/-- `lane.Lane2U32.zero = .ok ⟨[0#u32, 0#u32], _⟩`. -/
private theorem lane_zero_eq_ok :
    (lane.Lane2U32.zero : Result lane.Lane2U32) =
      .ok ⟨[0#u32, 0#u32], by decide⟩ := by
  unfold lane.Lane2U32.zero
         libcrux_secrets.traits.Classify.Blanket.classify
         lane.Lane2U32.from_ints
  rfl

/-- `RATE / 8#usize` succeeds and returns a value `i` with `i.val = RATE.val / 8`. -/
private theorem rate_div_8_ok (RATE : Std.Usize) :
    ∃ i : Std.Usize, (RATE / 8#usize : Result Std.Usize) = .ok i
      ∧ i.val = RATE.val / 8 := by
  have h := Std.UScalar.div_bv_spec RATE (y := 8#usize) (by decide)
  obtain ⟨i, hi_eq, hi_val, _⟩ := h
  refine ⟨i, hi_eq, ?_⟩
  rw [hi_val]
  show RATE.val / (8#usize : Std.Usize).val = RATE.val / 8
  have h8 : (8#usize : Std.Usize).val = 8 := by decide
  rw [h8]

/-! ### Helpers for textbook-form posts. -/

/-- Indexing `Foundation.lift s` at a `Fin 25` returns the lifted
    interleaved halves of `s.st[k]`.  Public companion to the `private`
    `lift_getElem` in `Equivalence/ThetaLiftDefs.lean`. -/
private theorem lift_getElem_bytes (s : state.KeccakState) (k : Fin 25) :
    (Foundation.lift s).val[k.val]! =
      (⟨lift_lane_bv ((s.st.val[k.val]!).val[0]!.bv)
                     ((s.st.val[k.val]!).val[1]!.bv)⟩ : Std.U64) := by
  unfold Foundation.lift Foundation.lift_lane
  change (List.ofFn _)[k.val]! = _
  rw [getElem!_pos _ k.val (by simpa using k.isLt), List.getElem_ofFn]

/-- Bytewise readout for `BitVec.toLEBytes` over 64-bit values: byte `i` is
    `BitVec.ofNat 8 ((bv.toNat >>> (8*i)) &&& 0xff)`. Stated at the
    BitVec level. -/
private theorem toLEBytes64_getElem!_eq_ofNat_shift_and
    (bv : BitVec 64) (i : Nat) (hi : i < 8) :
    bv.toLEBytes[i]! = BitVec.ofNat 8 ((bv.toNat >>> (8 * i)) &&& 0xff) := by
  -- Each side is determined by its 8 bits (as Nats).
  apply BitVec.eq_of_toNat_eq
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 8
  · -- LHS bit j: use `BitVec.toLEBytes_getElem!_testBit`.
    -- RHS bit j: shift/and gives the (8i+j)-th bit of `bv.toNat`.
    have h_LHS_bit : (bv.toLEBytes[i]!).toNat.testBit j = bv.toNat.testBit (8 * i + j) := by
      have h := BitVec.toLEBytes_getElem!_testBit bv i j hj
      -- `h : Byte.testBit (toLEBytes[i]!) j = bv[8*i+j]!`
      -- `Byte.testBit b j = Nat.testBit b.toNat j` (by definition).
      -- `bv[8*i+j]! = bv.toNat.testBit (8*i+j)`.
      show Nat.testBit (bv.toLEBytes[i]!).toNat j = bv.toNat.testBit (8 * i + j)
      rw [show Nat.testBit (bv.toLEBytes[i]!).toNat j = Byte.testBit bv.toLEBytes[i]! j from rfl]
      rw [h, BitVec.getElem!_eq_testBit_toNat]
    rw [h_LHS_bit]
    -- RHS: `(BitVec.ofNat 8 ...).toNat = ... % 256`.
    simp only [BitVec.toNat_ofNat]
    have h_and_eq_mod : (bv.toNat >>> (8 * i)) &&& 0xff
                          = (bv.toNat >>> (8 * i)) % 256 := by
      show _ &&& 255 = _ % 256
      rw [show (255 : Nat) = 2^8 - 1 from by decide,
          show (256 : Nat) = 2^8 from by decide]
      exact Nat.and_two_pow_sub_one_eq_mod _ 8
    rw [h_and_eq_mod]
    rw [show (2^8 : Nat) = 256 from by decide]
    -- Goal: bv.toNat.testBit (8 * i + j) = (bv.toNat >>> (8 * i) % 256 % 256).testBit j
    have h_mm : (bv.toNat >>> (8 * i)) % 256 % 256 = (bv.toNat >>> (8 * i)) % 256 := by
      rw [Nat.mod_mod]
    rw [h_mm]
    rw [show (256 : Nat) = 2^8 from by decide]
    rw [Nat.testBit_mod_two_pow]
    simp only [decide_true, Bool.true_and, hj, Nat.testBit_shiftRight]
  · -- Bits j ≥ 8 are 0 on both sides.
    have hLHS_isLt : (bv.toLEBytes[i]!).toNat < 256 := by
      have := bv.toLEBytes[i]!.isLt; simpa using this
    have h_jj : 8 ≤ j := by omega
    have h_pow : (256 : Nat) = 2^8 := by decide
    have hRHS_isLt : (BitVec.ofNat 8 ((bv.toNat >>> (8 * i)) &&& 0xff)).toNat < 256 := by
      have := (BitVec.ofNat 8 ((bv.toNat >>> (8 * i)) &&& 0xff)).isLt
      have h_pow2 : (2 ^ 8 : Nat) = 256 := by decide
      omega
    have hLHS : (bv.toLEBytes[i]!).toNat.testBit j = false := by
      rw [Nat.testBit_eq_false_of_lt]
      calc (bv.toLEBytes[i]!).toNat < 256 := hLHS_isLt
        _ = 2 ^ 8 := h_pow
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) h_jj
    have hRHS : (BitVec.ofNat 8 ((bv.toNat >>> (8 * i)) &&& 0xff)).toNat.testBit j = false := by
      rw [Nat.testBit_eq_false_of_lt]
      calc (BitVec.ofNat 8 ((bv.toNat >>> (8 * i)) &&& 0xff)).toNat < 256 := hRHS_isLt
        _ = 2 ^ 8 := h_pow
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) h_jj
    rw [hLHS, hRHS]

/-- `store_block_byte_at s b` (the value the strong store-loop produces at
    byte position `b`) equals byte `b%8` of the LE-byte split of the spec-side
    `(Foundation.lift s).val[5*((b/8)%5) + (b/8)/5]!`. -/
private theorem store_block_byte_at_eq_toLEBytes
    (s : state.KeccakState) (b : Nat) (hb : b / 8 < 25) :
    store_block_byte_at s b =
      ⟨(BitVec.toLEBytes
          ((Foundation.lift s).val[5 * ((b / 8) % 5) + (b / 8) / 5]!).bv)[b % 8]!⟩ := by
  -- Unfold store_block_byte_at; LHS is ⟨BitVec.ofNat 8 ((u64.bv.toNat >>> (8*(b%8))) &&& 0xff)⟩.
  unfold store_block_byte_at
  -- p < 25.
  have hp_lt : 5 * ((b / 8) % 5) + (b / 8) / 5 < 25 := by
    have h1 : (b / 8) % 5 < 5 := Nat.mod_lt _ (by decide)
    have h2 : (b / 8) / 5 < 5 :=
      (Nat.div_lt_iff_lt_mul (by decide : 0 < 5)).mpr (by omega)
    omega
  -- (Foundation.lift s).val[p]!.bv = lift_lane_bv ...
  have h_lift : ((Foundation.lift s).val[5 * ((b / 8) % 5) + (b / 8) / 5]!).bv =
      lift_lane_bv
        ((s.st.val[5 * ((b / 8) % 5) + (b / 8) / 5]!).val[0]!).bv
        ((s.st.val[5 * ((b / 8) % 5) + (b / 8) / 5]!).val[1]!).bv := by
    rw [lift_getElem_bytes s ⟨_, hp_lt⟩]
  -- `lift_lane (s.st.val[p]!)).bv = lift_lane_bv ...` (by lift_lane def).
  have h_ll_bv :
      (Foundation.lift_lane (s.st.val[5 * ((b / 8) % 5) + (b / 8) / 5]!)).bv =
        lift_lane_bv
          ((s.st.val[5 * ((b / 8) % 5) + (b / 8) / 5]!).val[0]!).bv
          ((s.st.val[5 * ((b / 8) % 5) + (b / 8) / 5]!).val[1]!).bv := rfl
  have hb_mod : b % 8 < 8 := Nat.mod_lt _ (by decide)
  -- Both sides are `⟨BitVec 8⟩ = Std.U8`; reduce to the BitVec equality.
  apply Std.UScalar.eq_of_val_eq
  show (BitVec.ofNat 8 _).toNat = _
  -- Reduce the RHS via the toLEBytes lemma.
  have h_bytes := toLEBytes64_getElem!_eq_ofNat_shift_and
    ((Foundation.lift s).val[5 * ((b / 8) % 5) + (b / 8) / 5]!).bv
    (b % 8) hb_mod
  rw [h_bytes, h_lift]
  -- Both sides are now `BitVec.ofNat 8 ((lift_lane_bv _ _).toNat >>> (8*(b%8)) &&& 0xff)`.
  rfl

/-! ### Top-level Triples. -/

/-- `state.KeccakState.load_block RATE s blocks start` terminates with
    `.ok` whenever the standard sponge preconditions hold:
    `RATE.val ≤ 200`, `RATE.val % 8 = 0`, the byte window
    `[start, start+RATE)` fits inside `blocks`, and the offset arithmetic
    does not overflow.

    The two underlying loops walk `i ∈ [0, RATE/8) ⊆ [0, 25)` reading
    8-byte windows of `blocks` and updating the 25-cell `state_flat` then
    XORing into the impl's interleaved Keccak state. The body Triples
    are in `Sponge/LoopSpecs.lean`. -/
@[spec]
theorem state.KeccakState.load_block_spec
    (RATE : Std.Usize) (s : state.KeccakState) (blocks : Slice Std.U8)
    (start : Std.Usize)
    (h_RATE_mod : RATE.val % 8 = 0)
    (h_RATE_bnd : RATE.val ≤ 200)
    (h_blk  : start.val + RATE.val ≤ blocks.val.length)
    (h_off  : start.val + RATE.val ≤ Std.Usize.max) :
    ⦃ ⌜ True ⌝ ⦄
    state.KeccakState.load_block RATE s blocks start
    ⦃ ⇓ r => ⌜
        r.i = s.i
        ∧ ∀ k : Nat, k < 25 →
            ((Foundation.lift r).val[k]!).bv =
              (if 5 * (k % 5) + k / 5 < RATE.val / 8 then
                  ((Foundation.lift s).val[k]!).bv ^^^
                    (BitVec.zeroExtend 64
                        (((Lane2U32_from_4byte_LE_pairs blocks start
                            (5 * (k % 5) + k / 5)).val[1]!).bv) <<< 32
                     ||| BitVec.zeroExtend 64
                        (((Lane2U32_from_4byte_LE_pairs blocks start
                            (5 * (k % 5) + k / 5)).val[0]!).bv))
               else ((Foundation.lift s).val[k]!).bv)
    ⌝ ⦄ := by
  have h_blk_len : RATE.val ≤ blocks.val.length := by omega
  have h_RATE_div_le : RATE.val / 8 ≤ 25 := by omega
  have h_RATE_div_mul : 8 * (RATE.val / 8) = RATE.val := by
    have : RATE.val = 8 * (RATE.val / 8) + RATE.val % 8 :=
      (Nat.div_add_mod _ _).symm
    omega
  -- Compute the .ok values of each step in `state.load_block_2u32`.
  have h_len := core_slice_len_eq_ok blocks
  have h_RATE_le : RATE.val ≤ (Std.Slice.len blocks).val := by
    rw [Std.Slice.len_val]; exact h_blk_len
  have h_mod := rate_mod_8_eq_ok RATE h_RATE_mod
  have h_zero := lane_zero_eq_ok
  obtain ⟨i2, h_div_eq, h_i2_val⟩ := rate_div_8_ok RATE
  -- Bounds for loop0.
  have h_loop0_le : (0#usize : Std.Usize).val ≤ i2.val := by
    show 0 ≤ i2.val; omega
  have h_loop0_bnd : i2.val ≤ 25 := by rw [h_i2_val]; exact h_RATE_div_le
  have h_loop0_off : start.val + 8 * i2.val ≤ Std.Usize.max := by
    rw [h_i2_val]; omega
  have h_loop0_blk : start.val + 8 * i2.val ≤ blocks.val.length := by
    rw [h_i2_val]; omega
  let state_flat : Std.Array lane.Lane2U32 25#usize :=
    Std.Array.repeat 25#usize (⟨[0#u32, 0#u32], by decide⟩ : lane.Lane2U32)
  obtain ⟨state_flat1, h_loop0_eq, h_state_flat1⟩ :=
    triple_exists_ok_bytes
      (state.load_block_2u32_loop0_spec
        ⟨0#usize, i2⟩ blocks start state_flat
        h_loop0_le h_loop0_bnd h_loop0_off h_loop0_blk (by rfl))
  obtain ⟨r_final, h_loop1_eq, h_post⟩ :=
    triple_exists_ok_bytes
      (state.load_block_2u32_loop1_spec
        ⟨0#usize, i2⟩ state_flat1 s h_loop0_le h_loop0_bnd rfl)
  obtain ⟨h_r_i, h_post2⟩ := h_post
  obtain ⟨h_lanes, h_unchanged⟩ := h_post2
  -- Build the per-cell BV post.
  have h_per_cell : ∀ k : Nat, k < 25 →
      ((Foundation.lift r_final).val[k]!).bv =
        (if 5 * (k % 5) + k / 5 < RATE.val / 8 then
            ((Foundation.lift s).val[k]!).bv ^^^
              (BitVec.zeroExtend 64
                  (((Lane2U32_from_4byte_LE_pairs blocks start
                      (5 * (k % 5) + k / 5)).val[1]!).bv) <<< 32
               ||| BitVec.zeroExtend 64
                  (((Lane2U32_from_4byte_LE_pairs blocks start
                      (5 * (k % 5) + k / 5)).val[0]!).bv))
         else ((Foundation.lift s).val[k]!).bv) := by
    intro k hk_25
    -- Apply lift_getElem_bytes at k.
    rw [lift_getElem_bytes r_final ⟨k, hk_25⟩,
        lift_getElem_bytes s ⟨k, hk_25⟩]
    show lift_lane_bv (r_final.st.val[k]!.val[0]!.bv) (r_final.st.val[k]!.val[1]!.bv) = _
    -- Let b = 5*(k%5) + k/5. By involution, k = 5*(b%5) + b/5.
    set b := 5 * (k % 5) + k / 5 with hb_def
    have hk_div_5 : k / 5 < 5 := by
      have : k < 5 * 5 := by omega
      exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 5)).mpr this
    have hk_mod_5 : k % 5 < 5 := Nat.mod_lt _ (by decide)
    have hb_lt_25 : b < 25 := by show 5 * (k % 5) + k / 5 < 25; omega
    -- k = 5 * (b % 5) + b / 5.
    have h_b_mod : b % 5 = k / 5 := by
      show (5 * (k % 5) + k / 5) % 5 = k / 5
      rw [Nat.add_comm, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hk_div_5
    have h_b_div : b / 5 = k % 5 := by
      show (5 * (k % 5) + k / 5) / 5 = k % 5
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by decide : 0 < 5)]
      have : k / 5 / 5 = 0 := Nat.div_eq_of_lt hk_div_5
      omega
    have h_inv : 5 * (b % 5) + b / 5 = k := by
      rw [h_b_mod, h_b_div]; omega
    by_cases h_b_lt : b < RATE.val / 8
    · -- The lane was touched in Loop1. Use h_lanes and the interleave identity.
      rw [if_pos h_b_lt]
      have h_b_lt_i2 : b < i2.val := by rw [h_i2_val]; exact h_b_lt
      -- Loop1's strong post for j = b: lift_lane_bv r.st[5*(b%5)+b/5] = loop1_lane_at s state_flat1 b.
      have h_lane := h_lanes b h_b_lt_i2 hb_lt_25
      -- The index 5*(b%5)+b/5 = k.
      rw [h_inv] at h_lane
      -- Loop0's post for j = b: state_flat1[b] is the interleave_bv pair.
      have h_sf := h_state_flat1 b h_b_lt_i2 hb_lt_25
      -- Unfold loop1_lane_at and apply lift_lane_bv_xor.
      rw [h_lane]
      unfold loop1_lane_at
      -- Goal: lift_lane_bv (s_lane[0].bv ^^^ state_flat1[b][0].bv)
      --                    (s_lane[1].bv ^^^ state_flat1[b][1].bv)
      --     = lift_lane_bv s.st[k].val[0].bv s.st[k].val[1].bv ^^^
      --       (((Lane2U32_from_4byte_LE_pairs...).val[1].bv.zeroExtend 64) <<< 32 |||
      --        (Lane2U32_from_4byte_LE_pairs...).val[0].bv.zeroExtend 64)
      simp only [h_inv]
      rw [← lift_lane_bv_xor]
      apply congrArg ((lift_lane_bv (s.st.val[k]!.val[0]!.bv) (s.st.val[k]!.val[1]!.bv)) ^^^ ·)
      -- Goal: lift_lane_bv state_flat1[b].val[0].bv state_flat1[b].val[1].bv = ...zeroExtend...
      -- From h_sf: ((state_flat1[b])[0].bv, (state_flat1[b])[1].bv) = interleave_bv (...) (...).
      have h_sf1 : (state_flat1.val[b]!).val[0]!.bv =
          (interleave_bv ((Lane2U32_from_4byte_LE_pairs blocks start b).val[0]!).bv
                         ((Lane2U32_from_4byte_LE_pairs blocks start b).val[1]!).bv).1 := by
        have := h_sf; exact (Prod.mk.injEq .. |>.mp this).1
      have h_sf2 : (state_flat1.val[b]!).val[1]!.bv =
          (interleave_bv ((Lane2U32_from_4byte_LE_pairs blocks start b).val[0]!).bv
                         ((Lane2U32_from_4byte_LE_pairs blocks start b).val[1]!).bv).2 := by
        have := h_sf; exact (Prod.mk.injEq .. |>.mp this).2
      rw [h_sf1, h_sf2]
      -- Apply interleave_bv_lift_eq.
      have h_ib := interleave_bv_lift_eq
        ((Lane2U32_from_4byte_LE_pairs blocks start b).val[0]!).bv
        ((Lane2U32_from_4byte_LE_pairs blocks start b).val[1]!).bv
      -- h_ib is `let (e,o) := ... in lift_lane_bv e o = ...`.
      simp only at h_ib
      exact h_ib
    · -- Untouched lane. Use h_unchanged.
      rw [if_neg h_b_lt]
      have h_b_ge_i2 : i2.val ≤ b := by rw [h_i2_val]; omega
      have h_unch := h_unchanged b h_b_ge_i2 hb_lt_25
      -- h_unch : r_final.st.val[5*(b%5)+b/5]! = s.st.val[5*(b%5)+b/5]!
      rw [h_inv] at h_unch
      rw [h_unch]
  -- Assemble: walk the body of `load_block`, rewriting each step.
  apply triple_of_ok_bytes (v := r_final) _ ⟨h_r_i, h_per_cell⟩
  show state.KeccakState.load_block RATE s blocks start = .ok r_final
  unfold state.KeccakState.load_block state.load_block_2u32
  -- Chain rewrites of the pure `.ok`-steps.
  rw [h_len]; simp only [bind_tc_ok]
  -- massert (RATE ≤ blocks.len) — uses `≤` which here unfolds to `decide ... = true`.
  show (do massert (RATE ≤ Std.Slice.len blocks); _) = .ok r_final
  unfold massert
  rw [if_pos (by show RATE ≤ Std.Slice.len blocks;
                  exact (Std.UScalar.le_equiv RATE _).mpr h_RATE_le)]
  simp only [bind_tc_ok]
  rw [h_mod]; simp only [bind_tc_ok]
  show (do massert ((0#usize : Std.Usize) = (0#usize : Std.Usize)); _) = .ok r_final
  unfold massert
  rw [if_pos (by rfl)]
  simp only [bind_tc_ok]
  rw [h_zero]; simp only [bind_tc_ok]
  rw [h_div_eq]; simp only [bind_tc_ok]
  rw [h_loop0_eq]; simp only [bind_tc_ok]
  exact h_loop1_eq

/-- `state.KeccakState.store_block RATE s out` terminates with `.ok`,
    and the output slice's length is preserved. Preconditions match
    those of `store_block_2u32_loop_spec` after derivation through the
    outer wrapper. -/
@[spec]
theorem state.KeccakState.store_block_spec
    (RATE : Std.Usize) (s : state.KeccakState) (out : Slice Std.U8)
    (h_RATE_mod : RATE.val % 8 = 0)
    (h_RATE_bnd : RATE.val ≤ 200)
    (h_blk  : RATE.val ≤ out.val.length)
    (h_off  : RATE.val ≤ Std.Usize.max) :
    ⦃ ⌜ True ⌝ ⦄
    state.KeccakState.store_block RATE s out
    ⦃ ⇓ r => ⌜
        r.val.length = out.val.length
        ∧ ∀ k : Nat, k < RATE.val →
            r.val[k]! = ⟨(BitVec.toLEBytes
              ((Foundation.lift s).val[5 * ((k / 8) % 5) + (k / 8) / 5]!).bv)[k % 8]!⟩
    ⌝ ⦄ := by
  have h_RATE_div_le : RATE.val / 8 ≤ 25 := by omega
  have h_RATE_div_mul : 8 * (RATE.val / 8) = RATE.val := by
    have : RATE.val = 8 * (RATE.val / 8) + RATE.val % 8 :=
      (Nat.div_add_mod _ _).symm
    omega
  obtain ⟨i_div, h_div_eq, h_div_val⟩ := rate_div_8_ok RATE
  have h_loop_le : (0#usize : Std.Usize).val ≤ i_div.val := by
    show 0 ≤ i_div.val; omega
  have h_loop_bnd : i_div.val ≤ 25 := by rw [h_div_val]; exact h_RATE_div_le
  have h_loop_off : 8 * i_div.val ≤ Std.Usize.max := by
    rw [h_div_val]; omega
  have h_loop_blk : 8 * i_div.val ≤ out.val.length := by
    rw [h_div_val]; omega
  obtain ⟨r, h_r_eq, h_r_len, h_r_bytes⟩ :=
    triple_exists_ok_bytes
      (state.store_block_2u32_loop_spec ⟨0#usize, i_div⟩ s out
        h_loop_le h_loop_bnd h_loop_off h_loop_blk (by rfl))
  -- The loop's strong post gives `r.val[b]! = store_block_byte_at s b`
  -- for `b < 8 * i_div.val = 8 * (RATE.val / 8) = RATE.val` (when RATE.val%8=0).
  -- We rewrite via `store_block_byte_at_eq_toLEBytes`.
  have h_r_textbook : ∀ k : Nat, k < RATE.val →
      r.val[k]! = ⟨(BitVec.toLEBytes
        ((Foundation.lift s).val[5 * ((k / 8) % 5) + (k / 8) / 5]!).bv)[k % 8]!⟩ := by
    intro k hk_RATE
    have hk_8idiv : k < 8 * i_div.val := by rw [h_div_val]; omega
    have hk_200 : k < 8 * 25 := by omega
    have hk_div : k / 8 < 25 := by
      have : k < 8 * 25 := hk_200
      omega
    have h_loop := h_r_bytes k hk_8idiv hk_200
    -- h_loop : r.val[k]! = store_block_byte_at s k
    rw [h_loop]
    exact store_block_byte_at_eq_toLEBytes s k hk_div
  apply triple_of_ok_bytes (v := r) _ ⟨h_r_len, h_r_textbook⟩
  show state.KeccakState.store_block RATE s out = .ok r
  unfold state.KeccakState.store_block state.store_block_2u32
  simp only [h_div_eq, bind_tc_ok]
  exact h_r_eq

/-- `state.KeccakState.load_block_full RATE s blocks start` delegates to
    `load_block_2u32` after the `Array.to_slice` coercion. Same
    termination post as `load_block_spec`. -/
@[spec]
theorem state.KeccakState.load_block_full_spec
    (RATE : Std.Usize) (s : state.KeccakState)
    (blocks : Std.Array Std.U8 200#usize) (start : Std.Usize)
    (h_RATE_mod : RATE.val % 8 = 0)
    (h_RATE_bnd : RATE.val ≤ 200)
    (h_blk : start.val + RATE.val ≤ 200)
    (h_off : start.val + RATE.val ≤ Std.Usize.max) :
    ⦃ ⌜ True ⌝ ⦄
    state.KeccakState.load_block_full RATE s blocks start
    ⦃ ⇓ r => ⌜
        r.i = s.i
        ∧ ∀ k : Nat, k < 25 →
            ((Foundation.lift r).val[k]!).bv =
              (if 5 * (k % 5) + k / 5 < RATE.val / 8 then
                  ((Foundation.lift s).val[k]!).bv ^^^
                    (BitVec.zeroExtend 64
                        (((Lane2U32_from_4byte_LE_pairs (Std.Array.to_slice blocks) start
                            (5 * (k % 5) + k / 5)).val[1]!).bv) <<< 32
                     ||| BitVec.zeroExtend 64
                        (((Lane2U32_from_4byte_LE_pairs (Std.Array.to_slice blocks) start
                            (5 * (k % 5) + k / 5)).val[0]!).bv))
               else ((Foundation.lift s).val[k]!).bv)
    ⌝ ⦄ := by
  -- `Array.to_slice` preserves `.val`; the array has length 200.
  have h_to_slice_val : (Std.Array.to_slice blocks).val = blocks.val := rfl
  have h_to_slice_len : (Std.Array.to_slice blocks).val.length = 200 := by
    rw [h_to_slice_val]; exact blocks.property
  have h_blk' : start.val + RATE.val ≤ (Std.Array.to_slice blocks).val.length := by
    rw [h_to_slice_len]; exact h_blk
  obtain ⟨r_final, h_inner_eq, h_post⟩ :=
    triple_exists_ok_bytes
      (state.KeccakState.load_block_spec RATE s
        (Std.Array.to_slice blocks) start
        h_RATE_mod h_RATE_bnd h_blk' h_off)
  obtain ⟨h_r_i, h_r_per_cell⟩ := h_post
  have h_inner_unfold :
      state.load_block_2u32 RATE s (Std.Array.to_slice blocks) start = .ok r_final := by
    have := h_inner_eq; unfold state.KeccakState.load_block at this; exact this
  apply triple_of_ok_bytes (v := r_final) _ ⟨h_r_i, h_r_per_cell⟩
  show state.KeccakState.load_block_full RATE s blocks start = .ok r_final
  unfold state.KeccakState.load_block_full state.load_block_full_2u32
  -- The body is `do s1 ← lift (Array.to_slice blocks); load_block_2u32 RATE s s1 start`.
  -- For the public `Slice U8`, `lift` (here `Std.lift`) is `Result.ok` (identity).
  -- We reduce `lift x = .ok x` and then chain.
  show (do
        let s1 ← Std.lift (α := Slice Std.U8) (Std.Array.to_slice blocks)
        state.load_block_2u32 RATE s s1 start) = .ok r_final
  unfold Std.lift
  show (do
        let s1 ← (Result.ok (Std.Array.to_slice blocks) : Result (Slice Std.U8))
        state.load_block_2u32 RATE s s1 start) = .ok r_final
  simp only [bind_tc_ok]
  exact h_inner_unfold

end libcrux_iot_sha3.Sponge
