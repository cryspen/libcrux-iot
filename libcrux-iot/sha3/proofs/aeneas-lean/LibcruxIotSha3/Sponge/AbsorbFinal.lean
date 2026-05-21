/-
  # Phase 6 — `keccak.absorb_final` ↔ `sponge.absorb_final`

  This file delivers the Phase 6 main Triple `keccak.absorb_final_spec`
  with the **Partial-B post**:

  * termination of `keccak.absorb_final`;
  * `r.i.val = 0` on the result (consumed by Phase 7's squeeze-first-block
    precondition).

  The Plan-targeted full textbook post — adding the spec equation
  `sponge.absorb_final (lift s) last start len RATE DELIM = .ok (lift r)`
  — requires walking both the impl-side 4-step buffer construction and
  the spec-side `sponge.pad_last_block` in lock-step. This file lays the
  infrastructure (`padded_buf` def + Array `index_mut` Triple) needed to
  close that gap in a follow-up, but the final lock-step composition is
  deferred.

  ## Post landed here

  ```
  @[spec]
  theorem keccak.absorb_final_spec
      (RATE DELIM s last start len)
      (h_i : s.i.val = 0) (h_len_lt_RATE : len.val < RATE.val)
      (h_RATE_mod : RATE.val % 8 = 0) (h_RATE_ge_1 : 1 ≤ RATE.val)
      (h_RATE_le_200 : RATE.val ≤ 200)
      (h_last_len : start.val + len.val ≤ last.val.length)
      (h_off : start.val + len.val ≤ Std.Usize.max) :
      ⦃⌜True⌝⦄ keccak.absorb_final RATE DELIM s last start len ⦃⇓ r => ⌜r.i.val = 0⌝⦄
  ```

  ## See also

  - `Sponge/AbsorbBlock.lean` — `keccak.absorb_block_spec` (Phase-2
    composed Triple).
  - `Sponge/Plan.lean` § 6 — Plan target with full textbook post.
-/
import LibcruxIotSha3.Sponge.AbsorbBlock

open Aeneas Aeneas.Std Result Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Sponge

open libcrux_iot_sha3.Equivalence

-- Defensive seal re-issue: no proof in this file may unfold either side
-- of Bridge 1.
set_option allowUnsafeReducibility true in
attribute [local irreducible] keccak.keccakf1600 keccak_f.keccak_f

/-! ## Phase 6 — `keccak.absorb_final` ↔ `sponge.absorb_final`. -/

/-- Local triple-of-ok helper. -/
private theorem triple_of_ok_af {α : Type} {x : Result α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, hp]

/-- Local existence extractor. -/
private theorem triple_exists_ok_af {α : Type} {x : Result α}
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

/-! ### Array index_mut Triple over `Range Usize`.

The Array variant of `core_models_Slice_Insts_index_mut_RangeUsize_spec`
(SliceSpecs.lean). Routes through `Array.to_slice_mut`. -/
@[spec]
theorem core_models_Array_Insts_index_mut_RangeUsize_spec
    {T : Type} {N : Std.Usize} (arr : Std.Array T N)
    (r : core_models.ops.range.Range Std.Usize)
    (h0 : r.start.val ≤ r.end.val) (h1 : r.end.val ≤ N.val) :
    ⦃ ⌜ True ⌝ ⦄
    core_models.Array.Insts.Core_modelsOpsIndexIndexMut.index_mut
      (core_models.ops.range.RangeUsize.Insts.Core_modelsSliceIndexSliceIndexSliceSlice T) arr r
    ⦃ ⇓ p => ⌜ p.1.val = arr.val.slice r.start.val r.end.val ∧
                p.1.val.length = r.end.val - r.start.val ∧
                ∀ s' : Slice T, s'.val.length = r.end.val - r.start.val →
                  (p.2 s').val = arr.val.setSlice! r.start.val s'.val ⌝ ⦄ := by
  unfold core_models.Array.Insts.Core_modelsOpsIndexIndexMut.index_mut
  have h_to_slice_mut : Std.Array.to_slice_mut arr
      = (Std.Array.to_slice arr, Std.Array.from_slice arr) := rfl
  have h_val_to_slice : (Std.Array.to_slice arr).val = arr.val := Std.Array.val_to_slice arr
  have h_len_to_slice : (Std.Array.to_slice arr).val.length = N.val := by
    rw [h_val_to_slice]; exact arr.property
  have h1' : r.end.val ≤ (Std.Array.to_slice arr).val.length := by rw [h_len_to_slice]; exact h1
  have h_slice :=
    core_models_Slice_Insts_index_mut_RangeUsize_spec (Std.Array.to_slice arr) r h0 h1'
  obtain ⟨p_slice, hp_eq, hp_val, hp_len, hp_back⟩ := triple_exists_ok_af h_slice
  have h_slice_eq_core :
      (core.slice.index.Slice.index_mut
        (core_models.ops.range.RangeUsize.Insts.Core_modelsSliceIndexSliceIndexSliceSlice T)
        (Std.Array.to_slice arr) r) = .ok p_slice := by
    have := hp_eq
    unfold core_models.Slice.Insts.Core_modelsOpsIndexIndexMut.index_mut at this
    exact this
  set out_val := p_slice.1
  set to_slice_back := p_slice.2
  refine triple_of_ok_af (v := (out_val, fun o => Std.Array.from_slice arr (to_slice_back o))) ?_ ?_
  · show (do
      let (s, to_arr) := Std.Array.to_slice_mut arr
      let (out, ts) ← core.slice.index.Slice.index_mut
        (core_models.ops.range.RangeUsize.Insts.Core_modelsSliceIndexSliceIndexSliceSlice T)
        s r
      ok (out, fun o => to_arr (ts o))) = .ok _
    rw [h_to_slice_mut]
    simp only
    rw [h_slice_eq_core]; simp only [bind_tc_ok]
    rfl
  · refine ⟨?_, ?_, ?_⟩
    · show p_slice.1.val = arr.val.slice r.start.val r.end.val
      rw [hp_val, h_val_to_slice]
    · show p_slice.1.val.length = r.end.val - r.start.val
      exact hp_len
    · intro s' h_s'_len
      show (Std.Array.from_slice arr (to_slice_back s')).val = arr.val.setSlice! r.start.val s'.val
      have h_back_len : (to_slice_back s').val.length = N.val := by
        rw [hp_back s']
        rw [List.length_setSlice!]; exact h_len_to_slice
      rw [Std.Array.from_slice_val _ _ h_back_len]
      rw [hp_back s']
      rw [h_val_to_slice]

/-! ### `padded_buf` — the shared 4-step buffer value.

Both the impl's manual buffer construction and the spec's
`sponge.pad_last_block` produce this `Array U8 200` value. The follow-up
that lands the full textbook post will prove the impl/spec chains both
reduce to `.ok (padded_buf last start len i_r1 DELIM)`. -/
def padded_buf
    (last : Slice Std.U8) (start len i_r1 : Std.Usize) (DELIM : Std.U8) :
    Std.Array Std.U8 200#usize :=
  let buf0 : Std.Array Std.U8 200#usize := Std.Array.repeat 200#usize 0#u8
  let buf1_val : List Std.U8 :=
    if 0 < len.val then
      buf0.val.setSlice! 0 (last.val.slice start.val (start.val + len.val))
    else buf0.val
  let buf1 : Std.Array Std.U8 200#usize := ⟨buf1_val, by
    show (if 0 < len.val then buf0.val.setSlice! 0 (last.val.slice start.val (start.val + len.val))
          else buf0.val).length = (200#usize : Std.Usize).val
    split <;> simp [List.length_setSlice!, buf0.property]⟩
  let buf2 : Std.Array Std.U8 200#usize := buf1.set len DELIM
  buf2.set i_r1 (buf2.val[i_r1.val]! ||| 128#u8)

/-! ### Phase 6 main Triple. -/

/-- `keccak.absorb_final RATE DELIM s last start len`:
    build a 200-byte padded buffer (zero-init, copy `last[start..start+len]`,
    write `DELIM` at offset `len`, OR `0x80` into byte `RATE-1`), then
    load-and-permute the rate-window.

    **Partial-B post**: termination, `r.i.val = 0`. The Plan's textbook
    spec equation `sponge.absorb_final (lift s) ... = .ok (lift r)` is
    deferred to a follow-up commit (the infrastructure `padded_buf` and
    `core_models_Array_Insts_index_mut_RangeUsize_spec` are landed above).

    Preconditions match the impl's `massert (len < RATE)` plus the
    standard `RATE.val % 8 = 0`, `1 ≤ RATE.val ≤ 200`, and bounds for the
    byte-window inside `last`. -/
@[spec]
theorem keccak.absorb_final_spec
    (RATE : Std.Usize) (DELIM : Std.U8) (s : state.KeccakState)
    (last : Slice Std.U8) (start : Std.Usize) (len : Std.Usize)
    (h_i : s.i.val = 0)
    (h_len_lt_RATE : len.val < RATE.val)
    (h_RATE_mod : RATE.val % 8 = 0)
    (h_RATE_ge_1 : 1 ≤ RATE.val)
    (h_RATE_le_200 : RATE.val ≤ 200)
    (h_last_len : start.val + len.val ≤ last.val.length)
    (h_off : start.val + len.val ≤ Std.Usize.max) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.absorb_final RATE DELIM s last start len
    ⦃ ⇓ r => ⌜ r.i.val = 0 ⌝ ⦄ := by
  -- Common: RATE.val ≤ Std.Usize.max.
  have h_RATE_max : RATE.val ≤ Std.Usize.max := by
    have h200 : (200 : Nat) ≤ Std.Usize.max := by scalar_tac
    omega
  -- RATE - 1#usize = .ok i_r1, i_r1.val = RATE.val - 1.
  obtain ⟨i_r1, h_i_r1_eq, h_i_r1_val_eq, _⟩ :=
    Std.WP.spec_imp_exists
      (Std.UScalar.sub_bv_spec (x := RATE) (y := 1#usize) (by
        have h1 : (1#usize : Std.Usize).val = 1 := by decide
        rw [h1]; exact h_RATE_ge_1))
  have h_i_r1_val : i_r1.val = RATE.val - 1 := by
    rw [h_i_r1_val_eq]
    show RATE.val - (1#usize : Std.Usize).val = RATE.val - 1
    have h1 : (1#usize : Std.Usize).val = 1 := by decide
    rw [h1]
  have h_i_r1_lt_200 : i_r1.val < 200 := by rw [h_i_r1_val]; omega
  -- Show existence: ∃ buf3 r, keccak.absorb_final = .ok r ∧ r.i.val = 0.
  suffices h_exists :
      ∃ (r : state.KeccakState),
        keccak.absorb_final RATE DELIM s last start len = .ok r ∧
        r.i.val = 0 by
    obtain ⟨r, h_r_eq, h_r_i⟩ := h_exists
    exact triple_of_ok_af (v := r) h_r_eq h_r_i
  -- Compute the buffer chain's `.ok` value.
  -- Step values shared across branches.
  set buf0 : Std.Array Std.U8 200#usize := Std.Array.repeat 200#usize 0#u8 with hbuf0_def
  have h_classify_buf0 : libcrux_secrets.traits.Classify.Blanket.classify buf0
                        = (Result.ok buf0 : Result _) := rfl
  have h_classify_DELIM : libcrux_secrets.traits.Classify.Blanket.classify DELIM
                        = (Result.ok DELIM : Result _) := rfl
  have h_buf0_len : buf0.val.length = 200 := buf0.property
  have h_lift_or_eq : ∀ x : Std.U8, (Std.lift (x ||| 128#u8) : Result Std.U8) = .ok (x ||| 128#u8) := by
    intro x; rfl
  have h_ma : massert (len < RATE) = .ok () := by
    unfold massert
    rw [if_pos (by show len < RATE; exact (Std.UScalar.lt_equiv len RATE).mpr h_len_lt_RATE)]
  -- The buffer chain produces a `buf1` (the `if`-branch result) and from
  -- there to `buf3`. We unify via case analysis on `len > 0`.
  -- Build `buf1` directly as an `Array U8 200` whose `.val` matches the
  -- if-branch's value.
  set buf1_val : List Std.U8 :=
    if 0 < len.val then
      buf0.val.setSlice! 0 (last.val.slice start.val (start.val + len.val))
    else buf0.val with hbuf1_val_def
  have h_buf1_val_len : buf1_val.length = 200 := by
    rw [hbuf1_val_def]; split <;> simp [List.length_setSlice!, h_buf0_len]
  set buf1 : Std.Array Std.U8 200#usize := ⟨buf1_val, by
    show buf1_val.length = (200#usize : Std.Usize).val
    rw [h_buf1_val_len]; rfl⟩ with hbuf1_def
  -- update buf1 len DELIM = .ok buf2.
  have h_len_lt_buf1 : len.val < buf1.val.length := by
    have : buf1.val.length = 200 := h_buf1_val_len
    omega
  obtain ⟨buf2, h_buf2_eq, h_buf2_set⟩ :=
    Std.WP.spec_imp_exists (Std.Array.update_spec buf1 len DELIM h_len_lt_buf1)
  -- index_usize buf2 i_r1 = .ok delim_byte.
  have h_i_r1_lt_buf2 : i_r1.val < buf2.val.length := by
    have hlen : buf2.val.length = (200#usize : Std.Usize).val := buf2.property
    show i_r1.val < buf2.val.length
    rw [hlen]; show i_r1.val < 200; omega
  obtain ⟨delim_byte, h_idx_eq, h_idx_val⟩ :=
    Std.WP.spec_imp_exists (Std.Array.index_usize_spec buf2 i_r1 h_i_r1_lt_buf2)
  -- update buf2 i_r1 (delim_byte ||| 0x80) = .ok buf3.
  obtain ⟨buf3, h_buf3_eq, h_buf3_set⟩ :=
    Std.WP.spec_imp_exists
      (Std.Array.update_spec buf2 i_r1 (delim_byte ||| 128#u8) h_i_r1_lt_buf2)
  -- absorb_block_spec on (to_slice buf3, 0).
  have h_blk : (0#usize : Std.Usize).val + RATE.val ≤ (Std.Array.to_slice buf3).val.length := by
    have hlen : (Std.Array.to_slice buf3).val.length = 200 := by
      rw [Std.Array.val_to_slice]; exact buf3.property
    rw [hlen]; show 0 + RATE.val ≤ 200; omega
  have h_off' : (0#usize : Std.Usize).val + RATE.val ≤ Std.Usize.max := by
    show 0 + RATE.val ≤ Std.Usize.max; omega
  obtain ⟨r, h_r_eq, h_r_post⟩ :=
    triple_exists_ok_af
      (keccak.absorb_block_spec RATE s (Std.Array.to_slice buf3) 0#usize
        h_i h_RATE_mod h_RATE_le_200 h_blk h_off')
  obtain ⟨h_r_i, _h_r_spec⟩ := h_r_post
  -- absorb_block = load_block_full + keccakf1600 (after to_slice).
  have h_absorb_eq :
      (do
        let s1 ← state.KeccakState.load_block_full RATE s buf3 0#usize
        keccak.keccakf1600 s1)
      = keccak.absorb_block RATE s (Std.Array.to_slice buf3) 0#usize := by
    unfold keccak.absorb_block
    unfold state.KeccakState.load_block_full state.load_block_full_2u32
    unfold state.KeccakState.load_block
    show (do
            let s1 ← (do
                        let s2 ← Std.lift (α := Slice Std.U8) (Std.Array.to_slice buf3)
                        state.load_block_2u32 RATE s s2 0#usize)
            keccak.keccakf1600 s1) = (do
            let s1 ← state.load_block_2u32 RATE s (Std.Array.to_slice buf3) 0#usize
            keccak.keccakf1600 s1)
    unfold Std.lift
    show (do
            let s1 ← (do
                        let s2 ← (Result.ok (Std.Array.to_slice buf3) : Result (Slice Std.U8))
                        state.load_block_2u32 RATE s s2 0#usize)
            keccak.keccakf1600 s1) = _
    simp only [bind_tc_ok]
  -- The if-branch produces `.ok buf1`. We prove this via case analysis.
  have h_if_eq :
      (if len > 0#usize
        then
          (do
            let (s, index_mut_back) ←
              core_models.Array.Insts.Core_modelsOpsIndexIndexMut.index_mut
                (core_models.Slice.Insts.Core_modelsOpsIndexIndexMut
                  (core_models.ops.range.RangeUsize.Insts.Core_modelsSliceIndexSliceIndexSliceSlice
                    Std.U8)) buf0 { start := 0#usize, «end» := len }
            let i ← start + len
            let s2 ←
              core_models.Slice.Insts.Core_modelsOpsIndexIndex.index
                (core_models.ops.range.RangeUsize.Insts.Core_modelsSliceIndexSliceIndexSliceSlice
                  Std.U8) last { start, «end» := i }
            let s3 ←
              core_models.slice.Slice.copy_from_slice
                core_models.U8.Insts.Core_modelsMarkerCopy s s2
            ok (index_mut_back s3))
        else (ok buf0 : Result (Std.Array Std.U8 200#usize)))
        = .ok buf1 := by
    by_cases hlen : (len > 0#usize)
    · rw [if_pos hlen]
      have h_len_val_pos : 0 < len.val := by
        have := (Std.UScalar.lt_equiv 0#usize len).mp hlen
        show 0 < len.val; omega
      have h_im_le : ((0#usize : Std.Usize).val) ≤ len.val := by show 0 ≤ len.val; omega
      have h_im_bnd : len.val ≤ (200#usize : Std.Usize).val := by show len.val ≤ 200; omega
      have h_wrap_eq_im :
          core_models.Slice.Insts.Core_modelsOpsIndexIndexMut
            (core_models.ops.range.RangeUsize.Insts.Core_modelsSliceIndexSliceIndexSliceSlice Std.U8)
          = core_models.ops.range.RangeUsize.Insts.Core_modelsSliceIndexSliceIndexSliceSlice Std.U8 := rfl
      rw [h_wrap_eq_im]
      obtain ⟨p_im, h_pim_eq, h_pim_val, h_pim_len, h_pim_back⟩ :=
        triple_exists_ok_af
          (core_models_Array_Insts_index_mut_RangeUsize_spec
            buf0 { start := 0#usize, «end» := len } h_im_le h_im_bnd)
      rw [h_pim_eq]; simp only [bind_tc_ok]
      obtain ⟨s_im, write_back⟩ := p_im
      simp only at h_pim_val h_pim_len h_pim_back ⊢
      -- The destructure pattern `let (s, im_back) := (s_im, write_back)` doesn't auto-reduce.
      -- Use `show` to manually beta-reduce.
      show (do
              let i ← start + len
              let s2 ← core_models.Slice.Insts.Core_modelsOpsIndexIndex.index
                (core_models.ops.range.RangeUsize.Insts.Core_modelsSliceIndexSliceIndexSliceSlice
                  Std.U8) last { start, «end» := i }
              let s3 ← core_models.slice.Slice.copy_from_slice
                core_models.U8.Insts.Core_modelsMarkerCopy s_im s2
              ok (write_back s3)) = _
      obtain ⟨i_sl, h_i_sl_eq, h_i_sl_val_eq, _⟩ :=
        Std.WP.spec_imp_exists
          (Std.UScalar.add_bv_spec (x := start) (y := len) (by scalar_tac))
      have h_i_sl_val : i_sl.val = start.val + len.val := h_i_sl_val_eq
      rw [h_i_sl_eq]; simp only [bind_tc_ok]
      have h_idx_le : start.val ≤ i_sl.val := by rw [h_i_sl_val]; omega
      have h_idx_bnd : i_sl.val ≤ last.val.length := by rw [h_i_sl_val]; omega
      obtain ⟨q, hq_eq, hq_val, hq_len⟩ :=
        triple_exists_ok_af
          (core_models_Slice_Insts_index_RangeUsize_spec
            last { start, «end» := i_sl } h_idx_le h_idx_bnd)
      rw [hq_eq]; simp only [bind_tc_ok]
      have h_p_q_len : s_im.val.length = q.val.length := by
        rw [h_pim_len, hq_len]
        show len.val - (0#usize : Std.Usize).val = i_sl.val - start.val
        rw [show ((0#usize : Std.Usize).val : Nat) = 0 from rfl, Nat.sub_zero, h_i_sl_val]
        omega
      obtain ⟨w, hw_eq, hw_val⟩ :=
        triple_exists_ok_af
          (core_models_slice_Slice_copy_from_slice_spec
            core_models.U8.Insts.Core_modelsMarkerCopy s_im q h_p_q_len)
      rw [hw_eq]; simp only [bind_tc_ok]
      -- Conclude write_back w = buf1.
      have h_w_val_len : w.val.length = len.val - (0#usize : Std.Usize).val := by
        rw [hw_val, hq_len]
        rw [show ((0#usize : Std.Usize).val : Nat) = 0 from rfl]
        rw [show i_sl.val - start.val = len.val from by rw [h_i_sl_val]; omega]
        rw [show len.val - 0 = len.val from by omega]
      have h_pback := h_pim_back w h_w_val_len
      have h_q_val_eq : q.val = last.val.slice start.val (start.val + len.val) := by
        rw [hq_val]
        show last.val.slice start.val i_sl.val = _
        rw [show i_sl.val = start.val + len.val from h_i_sl_val]
      apply Eq.symm
      show (Result.ok buf1 : Result (Std.Array Std.U8 200#usize)) = Result.ok (write_back w)
      congr 1
      apply Subtype.ext
      show buf1.val = (write_back w).val
      rw [h_pback, hw_val, h_q_val_eq]
      rw [hbuf1_def]
      show buf1_val = _
      rw [hbuf1_val_def, if_pos h_len_val_pos]
      show _ = buf0.val.setSlice! ((0#usize : Std.Usize).val) _
      rfl
    · rw [if_neg hlen]
      have h_len_val_zero : len.val = 0 := by
        have hle : ¬ (0 < len.val) := fun h => hlen ((Std.UScalar.lt_equiv 0#usize len).mpr (by show 0 < len.val; exact h))
        omega
      apply Eq.symm
      show (Result.ok buf1 : Result (Std.Array Std.U8 200#usize)) = Result.ok buf0
      congr 1
      apply Subtype.ext
      show buf1.val = buf0.val
      rw [hbuf1_def]; show buf1_val = buf0.val
      rw [hbuf1_val_def, if_neg (by omega : ¬ 0 < len.val)]
  -- Assemble the impl-side equation.
  refine ⟨r, ?_, h_r_i⟩
  unfold keccak.absorb_final
  -- Skip the `show` — work directly with the desugared form.
  rw [h_ma]; simp only [bind_tc_ok]
  -- `Array.repeat 200#usize 0#u8` is definitionally `buf0`, so `classify
  -- (Array.repeat ...)` reduces. We apply `rw` directly on `classify`.
  -- The let-bind for `a` is a `have` after simp.
  simp only [hbuf0_def.symm]
  rw [h_classify_buf0]; simp only [bind_tc_ok]
  -- The `if-let-bind` desugars with __do_jp. Rewrite the if-branch's
  -- value to `.ok buf1` directly using h_if_eq, by manipulating the
  -- desugared form.
  rw [h_if_eq]
  -- Now blocks1 := buf1; continue.
  simp only [bind_tc_ok]
  rw [h_classify_DELIM]; simp only [bind_tc_ok]
  rw [h_buf2_eq]; simp only [bind_tc_ok]
  rw [h_i_r1_eq]; simp only [bind_tc_ok]
  rw [h_idx_eq]; simp only [bind_tc_ok]
  rw [h_lift_or_eq delim_byte]; simp only [bind_tc_ok]
  rw [h_buf3_eq]; simp only [bind_tc_ok]
  rw [h_absorb_eq]
  exact h_r_eq

end libcrux_iot_sha3.Sponge
