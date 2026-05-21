/-
  # Phase 2 — `keccak.absorb_block` ↔ `sponge.absorb_block`

  This file hosts the single top-level `@[spec]` Triple bridging the
  impl's `keccak.absorb_block` to the sponge spec's `sponge.absorb_block`.

  ## Composition

  Impl side (`Extraction/Funs.lean:4306`):
  ```
  def keccak.absorb_block RATE s blocks start := do
    let s1 ← state.KeccakState.load_block RATE s blocks start
    keccak.keccakf1600 s1
  ```

  Spec side (`HacspecSha3/Extraction/Funs.lean:1157`):
  ```
  def sponge.absorb_block state block rate := do
    let state1 ← sponge.xor_block_into_state state block rate
    keccak_f.keccak_f state1
  ```

  ## Post strength (Phase 2 — Partial-B landed 2026-05-21)

  The Triple here carries the `r.i.val = 0` clause needed by Phase 3's
  chain (the next `absorb_block`'s precondition).

  The full "textbook" post

      ⦃ True ⦄ sponge.absorb_block (lift s) <block> RATE
        ⦃ ⇓ s' => s' = lift r ⦄

  is **deferred**: it would chain through the per-cell BV post of
  `load_block_spec` (in `Sponge/Bytes.lean`) and the per-cell
  `xor_block_value_at` post of `sponge_xor_block_into_state_spec` (in
  `Sponge/XorBlockSpec.lean`), but the two characterizations are
  expressed in different forms and need a bridge lemma
  (`xor_block_value_at ↔ BV interleave`) that is part of the deferred
  Phase 1a strong-loop work — see the comment in `Sponge/Bytes.lean`
  (top-of-file, "Phase 1a closer report"). The current weak post
  (`r.i.val = 0`) is sufficient for Phase 3 chaining (which only needs
  termination + `r.i.val = 0`).

  ## See also

  - `Sponge/Plan.lean` § 2 — full Plan post target.
  - `Sponge/Opaque.lean` — `keccakf1600_seal_spec`.
  - `Sponge/Bytes.lean` — `state.KeccakState.load_block_spec`.
-/
import LibcruxIotSha3.Sponge.Bytes

open Aeneas Aeneas.Std Result Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Sponge

open libcrux_iot_sha3.Equivalence

-- Defensive seal re-issue: no proof in this file may unfold either side
-- of Bridge 1.
set_option allowUnsafeReducibility true in
attribute [local irreducible] keccak.keccakf1600 keccak_f.keccak_f

/-! ## Phase 2 — `keccak.absorb_block` ↔ `sponge.absorb_block`. -/

/-- Local triple-of-ok helper. -/
private theorem triple_of_ok_ab {α : Type} {x : Result α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, hp]

/-- Local existence extractor: a Triple yields `∃ v, x = .ok v ∧ P v`. -/
private theorem triple_exists_ok_ab {α : Type} {x : Result α}
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

/-- `keccak.absorb_block RATE s blocks start` — XOR a `RATE`-byte block
    from `blocks` (at offset `start`) into the state, then apply the
    Keccak-f permutation.

    Phase 2 post (Partial-B): termination plus `r.i.val = 0`. The
    `r.i.val = 0` clause is what the next `absorb_block`'s precondition
    consumes in Phase 3. The full textbook post (spec-equality via
    `sponge.absorb_block`) is deferred — see file header. -/
@[spec]
theorem keccak.absorb_block_spec
    (RATE : Std.Usize) (s : state.KeccakState) (blocks : Slice Std.U8)
    (start : Std.Usize)
    (h_i : s.i.val = 0)
    (h_RATE_mod : RATE.val % 8 = 0)
    (h_RATE_bnd : RATE.val ≤ 200)
    (h_blk : start.val + RATE.val ≤ blocks.val.length)
    (h_off : start.val + RATE.val ≤ Std.Usize.max) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.absorb_block RATE s blocks start
    ⦃ ⇓ r => ⌜ r.i.val = 0 ⌝ ⦄ := by
  -- Step 1: discharge `load_block` via its @[spec] in Bytes.lean.
  obtain ⟨s1, h_s1_eq, h_s1_post⟩ :=
    triple_exists_ok_ab
      (state.KeccakState.load_block_spec RATE s blocks start
        h_RATE_mod h_RATE_bnd h_blk h_off)
  obtain ⟨h_s1_i, _h_s1_lanes⟩ := h_s1_post
  -- Step 2: discharge `keccakf1600` via its @[spec] in Opaque.lean.
  -- Need: s1.i.val = 0. We have s1.i = s.i, and s.i.val = 0 via h_i.
  have h_s1_i_val : s1.i.val = 0 := by rw [h_s1_i]; exact h_i
  obtain ⟨r, h_r_eq, h_r_post⟩ :=
    triple_exists_ok_ab (keccakf1600_seal_spec s1 h_s1_i_val)
  obtain ⟨_h_r_spec, h_r_i⟩ := h_r_post
  -- Step 3: assemble.
  apply triple_of_ok_ab (v := r) _ h_r_i
  show keccak.absorb_block RATE s blocks start = .ok r
  unfold keccak.absorb_block
  rw [h_s1_eq]; simp only [bind_tc_ok]
  exact h_r_eq

end libcrux_iot_sha3.Sponge
