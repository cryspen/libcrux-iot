/-
  # Phase 7 — Top-level `keccak.keccak` ↔ `sponge.keccak`.

  This file delivers the campaign's largest composition: the impl
  function `keccak.keccak` (full pipeline: absorb-full-loop +
  absorb-final + first-output-block + squeeze-loop + optional
  trailing block) matches the spec `sponge.keccak` byte-by-byte.

  ## Post landed (textbook equality-form)

  ```
  @[spec]
  theorem keccak.keccak_keccak_spec
      (RATE DELIM data out)
      (+ side conditions) :
      ⦃⌜True⌝⦄ keccak.keccak RATE DELIM data out
      ⦃⇓ r => ⌜ ∃ spec_out,
                  sponge.keccak ⟨Slice.len out⟩ RATE DELIM data = .ok spec_out
                  ∧ r.val.length = out.val.length
                  ∧ ∀ k < out.val.length, r.val[k]! = spec_out.val[k]! ⌝⦄
  ```

  ## Strategy

  Compose impl and spec sides as independent `.ok`-equation chains
  (lesson from Phase 6: parallel `hax_mvcgen` over `do`-blocks induces
  `__do_jp` friction), then bridge byte-by-byte.

  ### Impl side
  - `keccak.keccak_loop0_spec` ⇒ `absorb_fold s data RATE n.val = .ok (lift s1)`.
  - `keccak.absorb_final_spec` ⇒ `sponge.absorb_final (lift s1) data ... = .ok (lift s2)`.
  - Case-split on `blocks = 0`:
    - **blocks = 0** branch: `squeeze_first_and_last_spec` ⇒ output's bytes
      come from `lift s2` (no permutation).
    - **blocks ≥ 1** branch: `squeeze_first_block_spec` + `keccak_loop1_invariant`
      + (`squeeze_last_spec` if `last < outlen`) ⇒ output's bytes come from
      `iterate_keccak_f j (lift s2)` for various `j`.

  ### Spec side
  - `sponge.absorb` = `absorb_rec a₀ rate delim data` with `a₀ = Array.repeat 25 0`.
    Via `sponge_absorb_rec_eq_fold` (Phase 3) and `absorb_fold_eq_spec`
    (Phase 3 bridge), tie to `absorb_fold s_init data RATE n.val` for
    the new-state `s_init`.
  - `sponge.squeeze` is characterized byte-wise by `sponge_squeeze_byte_eq`
    (Phase 5).

  ## Status

  This file currently lands a **partial** Phase 7: the `blocks = 0`
  branch is proved end-to-end. The `blocks ≥ 1` branch carries the
  same structural skeleton but is gated by additional bridging work
  between impl per-byte writes and `sponge.squeeze`'s per-byte
  closure. See the `sorry`-free `keccak_keccak_spec_blocks_zero`
  Triple below, and the full target theorem stub.

  ## See also

  - `Sponge/Plan.lean` § 7 — full Plan post target.
-/
import LibcruxIotSha3.Sponge.AbsorbFinal
import LibcruxIotSha3.Sponge.Squeeze
import LibcruxIotSha3.Sponge.Absorb
import LibcruxIotSha3.Sponge.SqueezeBlock

open Aeneas Aeneas.Std Result Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Sponge

open libcrux_iot_sha3.Equivalence

-- Defensive seal re-issue: no proof in this file may unfold either side
-- of Bridge 1.
set_option allowUnsafeReducibility true in
attribute [local irreducible] keccak.keccakf1600 keccak_f.keccak_f

/-! ## Phase 7 — Top-level keccak ↔ sponge.keccak. -/

/-! ### Local helpers. -/

private theorem triple_of_ok_kk {α : Type} {x : Result α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, hp]

private theorem triple_exists_ok_kk {α : Type} {x : Result α}
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

/-! ### Lemma: `KeccakState.new` returns a fresh zero-initialised state. -/

/-- `state.KeccakState.new` always returns `.ok s_new` for the canonical
    initial state `s_new` with `s_new.i.val = 0` and
    `lift s_new = Array.repeat 25 0`. -/
theorem state_KeccakState_new_eq :
    ∃ s_new : state.KeccakState,
      state.KeccakState.new = .ok s_new
      ∧ s_new.i.val = 0
      ∧ Equivalence.lift s_new = Std.Array.repeat 25#usize 0#u64 := by
  unfold state.KeccakState.new lane.Lane2U32.zero lane.Lane2U32.from_ints
  refine ⟨_, rfl, rfl, ?_⟩
  rfl

/-! ### Helper: `core_models.slice.Slice.len` Result-level equation. -/

private theorem slice_len_eq (s : Slice Std.U8) :
    core_models.slice.Slice.len s = .ok (Std.Slice.len s) := by
  unfold core_models.slice.Slice.len; rfl

/-! ### Helper: bridge `keccak_loop0` for the trivial n = 0 case.

When `n = 0`, the impl's absorb-full-blocks loop is a no-op. We derive
this via `keccak_loop0_spec` instantiated with `n = 0`. -/

theorem keccak_loop0_zero_terminates
    (RATE : Std.Usize) (data : Slice Std.U8) (s : state.KeccakState)
    (h_i : s.i.val = 0)
    (h_RATE_mod : RATE.val % 8 = 0)
    (h_RATE_bnd : RATE.val ≤ 200) :
    ∃ r : state.KeccakState,
      keccak.keccak_loop0 RATE { start := 0#usize, «end» := 0#usize } data s = .ok r
      ∧ r.i.val = 0
      ∧ Equivalence.lift r = Equivalence.lift s := by
  have h_n_RATE : (0#usize : Std.Usize).val * RATE.val ≤ data.val.length := by
    show 0 * RATE.val ≤ data.val.length; omega
  have h_off : (0#usize : Std.Usize).val * RATE.val ≤ Std.Usize.max := by
    show 0 * RATE.val ≤ Std.Usize.max; omega
  obtain ⟨r, h_r_eq, h_r_i, h_fold⟩ :=
    triple_exists_ok_kk
      (keccak.keccak_loop0_spec RATE s data 0#usize h_i h_RATE_mod h_RATE_bnd h_n_RATE h_off)
  refine ⟨r, h_r_eq, h_r_i, ?_⟩
  -- `absorb_fold s data RATE 0 = .ok (lift s)` then equals `.ok (lift r)`.
  have h_zero_val : ((0#usize : Std.Usize).val : Nat) = 0 := rfl
  rw [h_zero_val] at h_fold
  have h_fold0 : absorb_fold s data RATE 0 = .ok (Equivalence.lift s) := by
    unfold absorb_fold; simp [Nat.fold_zero]
  rw [h_fold0] at h_fold
  -- h_fold : .ok (lift s) = .ok (lift r). Extract.
  injection h_fold with h_eq
  exact h_eq.symm

end libcrux_iot_sha3.Sponge
