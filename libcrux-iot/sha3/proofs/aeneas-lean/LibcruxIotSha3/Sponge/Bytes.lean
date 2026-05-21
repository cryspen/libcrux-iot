/-
  # Phase 1a — Byte ↔ Lane primitives (`load_block`, `store_block`,
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

  ## Post strength (Phase 1a, after 2026-05-21 strengthening pass — Partial-B)

  The three Triples here carry the **`i`-preservation** clause needed
  by Phase 2's absorb/squeeze chaining (`r.i.val = 0` precondition on
  the next `keccakf1600` call). Specifically:

  - `load_block_spec`: `⌜ r.i = s.i ⌝` (loop1 invariant carries it).
  - `store_block_spec`: `⌜ r.val.length = out.val.length ⌝` (returns a
     `Slice U8`, no state component).
  - `load_block_full_spec`: `⌜ r.i = s.i ⌝` (delegates to `load_block`).

  ## Phase 1a closer report (2026-05-21, extended)

  - **Task 1 (`xor_block_into_state_closure_call_mut_spec`) — LANDED**
    in `Sponge/XorBlockSpec.lean`. The per-cell `@[spec]` for the
    25-cell `from_fn` body drives the inner do-chain (div/rem →
    mul/add → div → if → slice-index → try_from → unwrap → from_le_bytes
    → lift | index_usize). The `b < rate/8` branch matches the
    constructed 8-byte array's `.val` with `list_8_at block.val (8b)`
    via `list_8_at_val_eq_slice`. Axioms: propext, Classical.choice,
    Quot.sound. **This unlocks Phase 2's spec-side composition.**

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
    weak posts are nonetheless sufficient for Phase 2 chaining
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
       ((Equivalence.lift s).val[5*((k/8)%5) + (k/8)/5]!).bv.toLEBytes[k%8]!`
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
  precondition. Phase 2 can now compose against them via `hax_mvcgen`
  to drive the absorb/squeeze loops at the impl side. The remaining
  spec-equation half is deferred to a follow-up pass once the loop-0
  /loop-1 strong invariants land. The Phase 1a closer (2026-05-21) landed
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
    posts targeting the strengthened phase.
  - `LibcruxIotSha3/Sponge/Opaque.lean` — Phase 0 seal of `keccakf1600`.
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

open libcrux_iot_sha3.Equivalence

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
    ⦃ ⇓ r => ⌜ r.i = s.i ⌝ ⦄ := by
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
  obtain ⟨state_flat1, h_loop0_eq, _⟩ :=
    triple_exists_ok_bytes
      (state.load_block_2u32_loop0_spec
        ⟨0#usize, i2⟩ blocks start state_flat
        h_loop0_le h_loop0_bnd h_loop0_off h_loop0_blk)
  obtain ⟨r_final, h_loop1_eq, h_r_i, _h_lanes⟩ :=
    triple_exists_ok_bytes
      (state.load_block_2u32_loop1_spec
        ⟨0#usize, i2⟩ state_flat1 s h_loop0_le h_loop0_bnd rfl)
  -- Assemble: walk the body of `load_block`, rewriting each step.
  apply triple_of_ok_bytes (v := r_final) _ h_r_i
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
    ⦃ ⇓ r => ⌜ r.val.length = out.val.length ⌝ ⦄ := by
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
  obtain ⟨r, h_r_eq, h_r_len⟩ :=
    triple_exists_ok_bytes
      (state.store_block_2u32_loop_spec ⟨0#usize, i_div⟩ s out
        h_loop_le h_loop_bnd h_loop_off h_loop_blk)
  apply triple_of_ok_bytes (v := r) _ h_r_len
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
    ⦃ ⇓ r => ⌜ r.i = s.i ⌝ ⦄ := by
  -- `Array.to_slice` preserves `.val`; the array has length 200.
  have h_to_slice_val : (Std.Array.to_slice blocks).val = blocks.val := rfl
  have h_to_slice_len : (Std.Array.to_slice blocks).val.length = 200 := by
    rw [h_to_slice_val]; exact blocks.property
  have h_blk' : start.val + RATE.val ≤ (Std.Array.to_slice blocks).val.length := by
    rw [h_to_slice_len]; exact h_blk
  obtain ⟨r_final, h_inner_eq, h_r_i⟩ :=
    triple_exists_ok_bytes
      (state.KeccakState.load_block_spec RATE s
        (Std.Array.to_slice blocks) start
        h_RATE_mod h_RATE_bnd h_blk' h_off)
  have h_inner_unfold :
      state.load_block_2u32 RATE s (Std.Array.to_slice blocks) start = .ok r_final := by
    have := h_inner_eq; unfold state.KeccakState.load_block at this; exact this
  apply triple_of_ok_bytes (v := r_final) _ h_r_i
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
