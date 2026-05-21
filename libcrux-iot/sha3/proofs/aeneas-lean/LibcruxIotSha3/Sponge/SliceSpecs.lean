/-
  # Phase 1a prerequisite — Aeneas Std byte/slice `@[spec]` Triples

  This file installs a set of small `@[spec]` Triples that the byte ↔
  lane bridges in `Sponge/Bytes.lean` will need to discharge. None of
  these have prior precedent in `LibcruxIotSha3/Equivalence/`; this file
  establishes the pattern.

  ## Installed (9 Triples)

  - `core_models_slice_Slice_len_spec` — `core_models.slice.Slice.len`
    returns the underlying list length.
  - `massert_spec` — `Aeneas.Std.massert b` succeeds (with `()`) when `b`.
  - `core_models_num_U32_from_le_bytes_spec`,
    `core_models_num_U32_to_le_bytes_spec` — byte ↔ u32 LE.
  - `core_models_num_U64_from_le_bytes_spec`,
    `core_models_num_U64_to_le_bytes_spec` — byte ↔ u64 LE.
  - `core_models_Slice_Insts_index_RangeUsize_spec` — slice subindexing
    over `Range<usize>` (used by load/store loops).
  - `core_models_Slice_Insts_index_mut_RangeUsize_spec` — mutable slice
    subindexing over `Range<usize>` (used by `store_block_2u32_loop.body`).
  - `core_models_result_Result_unwrap_spec` — `result.Result.unwrap` on
    `.Ok v` yields `v`.
  - `core_models_slice_Slice_copy_from_slice_spec` — write-into-slice;
    the impl model returns the source slice outright when lengths match.

  ## OMITTED

  - `core_models.Array.Insts.Core_modelsConvertTryFromShared0SliceTryFromSliceError.try_from`
    (`Slice T → Result (result.Result (Array T N) ...)`).
    The body invokes `rust_primitives.slice.array_from_fn` on the
    `try_from.closure`, whose Triple requires an induction over the
    closure's `call_mut` calls and the `List.range N.val` `foldlM`. The
    proof is mechanical but ~70 lines (closure step lemma + foldlM
    induction over `List.range'` + final list-rearrangement), so it is
    deferred. The Phase-1a campaign report tracks this gap.

  ## See also

  - `LibcruxIotSha3/Sponge/Plan.lean` § 1 for usage context.
  - `LibcruxIotSha3/Sponge/Bytes.lean` for the partial Phase-1a delivery
    of `load_block`/`store_block`/`load_block_full` Triples.
-/
import LibcruxIotSha3.Sponge.Opaque

open Aeneas Aeneas.Std Result Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Sponge

set_option allowUnsafeReducibility true in
attribute [local irreducible] keccak.keccakf1600 keccak_f.keccak_f

/-! ## Phase 1a prerequisite — Aeneas Std byte/slice `@[spec]` lemmas. -/

/-! ### `core_models.slice.Slice.len` -/

/-- The hax `core_models.slice.Slice.len` is a thin `pure`-wrapper around
    `Aeneas.Std.Slice.len`. Always succeeds with the underlying list length
    (as a `Usize`). -/
@[spec]
theorem core_models_slice_Slice_len_spec {T : Type} (s : Slice T) :
    ⦃ ⌜ True ⌝ ⦄
    core_models.slice.Slice.len s
    ⦃ ⇓ r => ⌜ r.val = s.val.length ⌝ ⦄ := by
  unfold core_models.slice.Slice.len
  simp [Triple, WP.wp]

/-! ### `Aeneas.Std.massert` -/

/-- `massert b` succeeds with `()` iff `b` holds. -/
@[spec]
theorem massert_spec (b : Prop) [Decidable b] (h : b) :
    ⦃ ⌜ True ⌝ ⦄
    massert b
    ⦃ ⇓ r => ⌜ r = () ⌝ ⦄ := by
  unfold massert
  simp [Triple, WP.wp, h]

/-! ### `core_models.num.U32.from_le_bytes` / `U32.to_le_bytes` -/

/-- The four-byte LE-load `U32.from_le_bytes` always succeeds with
    `core.num.U32.from_le_bytes` applied to the input array. -/
@[spec]
theorem core_models_num_U32_from_le_bytes_spec (bytes : Std.Array Std.U8 4#usize) :
    ⦃ ⌜ True ⌝ ⦄
    core_models.num.U32.from_le_bytes bytes
    ⦃ ⇓ r => ⌜ r = Std.core.num.U32.from_le_bytes bytes ⌝ ⦄ := by
  unfold core_models.num.U32.from_le_bytes rust_primitives.arithmetic.from_le_bytes_u32
  simp [Triple, WP.wp]

/-- The four-byte LE-store `U32.to_le_bytes` always succeeds with
    `core.num.U32.to_le_bytes` applied to the input integer. -/
@[spec]
theorem core_models_num_U32_to_le_bytes_spec (x : Std.U32) :
    ⦃ ⌜ True ⌝ ⦄
    core_models.num.U32.to_le_bytes x
    ⦃ ⇓ r => ⌜ r = Std.core.num.U32.to_le_bytes x ⌝ ⦄ := by
  unfold core_models.num.U32.to_le_bytes rust_primitives.arithmetic.to_le_bytes_u32
  simp [Triple, WP.wp]

/-! ### `core_models.num.U64.from_le_bytes` / `U64.to_le_bytes` -/

/-- The eight-byte LE-load `U64.from_le_bytes` always succeeds with
    `core.num.U64.from_le_bytes` applied to the input array. -/
@[spec]
theorem core_models_num_U64_from_le_bytes_spec (bytes : Std.Array Std.U8 8#usize) :
    ⦃ ⌜ True ⌝ ⦄
    core_models.num.U64.from_le_bytes bytes
    ⦃ ⇓ r => ⌜ r = Std.core.num.U64.from_le_bytes bytes ⌝ ⦄ := by
  unfold core_models.num.U64.from_le_bytes rust_primitives.arithmetic.from_le_bytes_u64
  simp [Triple, WP.wp]

/-- The eight-byte LE-store `U64.to_le_bytes` always succeeds with
    `core.num.U64.to_le_bytes` applied to the input integer. -/
@[spec]
theorem core_models_num_U64_to_le_bytes_spec (x : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄
    core_models.num.U64.to_le_bytes x
    ⦃ ⇓ r => ⌜ r = Std.core.num.U64.to_le_bytes x ⌝ ⦄ := by
  unfold core_models.num.U64.to_le_bytes rust_primitives.arithmetic.to_le_bytes_u64
  simp [Triple, WP.wp]

/-! ### `core_models.Slice.Insts.Core_modelsOpsIndexIndex.index` over `Range Usize` -/

/-- Slice subindexing over a `Range<usize>` succeeds whenever the range is
    in bounds, returning the sub-`Slice` whose `val` is the contiguous
    slice `s.val[start..end]`. -/
@[spec]
theorem core_models_Slice_Insts_index_RangeUsize_spec
    {T : Type} (s : Slice T) (r : core_models.ops.range.Range Std.Usize)
    (h0 : r.start.val ≤ r.end.val) (h1 : r.end.val ≤ s.val.length) :
    ⦃ ⌜ True ⌝ ⦄
    core_models.Slice.Insts.Core_modelsOpsIndexIndex.index
      (core_models.ops.range.RangeUsize.Insts.Core_modelsSliceIndexSliceIndexSliceSlice T) s r
    ⦃ ⇓ r' => ⌜ r'.val = s.val.slice r.start.val r.end.val ∧
                r'.val.length = r.end.val - r.start.val ⌝ ⦄ := by
  unfold core_models.Slice.Insts.Core_modelsOpsIndexIndex.index
         core_models.ops.range.RangeUsize.Insts.Core_modelsSliceIndexSliceIndexSliceSlice
         core_models.cmRangeUsizeToAeneas
         core.slice.index.Slice.index
         core.slice.index.SliceIndexRangeUsizeSlice.index
  have h0' : (⟨r.start, r.end⟩ : core.ops.range.Range Std.Usize).start
              ≤ (⟨r.start, r.end⟩ : core.ops.range.Range Std.Usize).end := by
    simpa [UScalar.le_equiv] using h0
  have h1' : (⟨r.start, r.end⟩ : core.ops.range.Range Std.Usize).end.val ≤ (Slice.length s) := by
    simpa [Slice.length] using h1
  simp only [Triple, WP.wp]
  simp [h0', h1', Slice.length]
  simp [List.slice, List.length_drop, List.length_take]
  omega

/-! ### `core_models.result.Result.unwrap`

The hax `Result.unwrap` on the `core_models` `result.Result` enum panics on
`Err` and returns the inner `T` on `Ok`. We give a Triple-style spec under
the precondition `r = .Ok v`.

NB: the `try_from` Triple (for `Slice U8 → Array U8 N`) is intentionally
OMITTED in this file. Its body invokes `rust_primitives.slice.array_from_fn`
on the `try_from.closure`, whose Triple requires a non-trivial inductive
proof over the closure's `call_mut` and the `List.range N.val` foldlM — a
much larger lemma that doesn't fit this file's footprint. The Phase-1a
report tracks this gap. -/

/-- `Result.unwrap` succeeds with `v` whenever the input is `.Ok v`. -/
@[spec]
theorem core_models_result_Result_unwrap_spec
    {T E : Type} (dbg : core_models.fmt.Debug E) (r : core_models.result.Result T E) (v : T)
    (h : r = .Ok v) :
    ⦃ ⌜ True ⌝ ⦄
    core_models.result.Result.unwrap dbg r
    ⦃ ⇓ r' => ⌜ r' = v ⌝ ⦄ := by
  unfold core_models.result.Result.unwrap
  subst h
  simp [Triple, WP.wp]

/-! ### `core_models.Slice.Insts.Core_modelsOpsIndexIndexMut.index_mut` over `Range Usize`

Used by `state.store_block_2u32_loop.body` (Funs.lean:4373) to obtain a
mutable sub-slice and a write-back closure. -/

/-- Mutable slice subindexing over a `Range<usize>` returns both the
    sub-slice (same `val` as the non-mut `index`) and a write-back
    closure that overwrites `s.val[r.start.val..]` with the argument's
    `val`. -/
@[spec]
theorem core_models_Slice_Insts_index_mut_RangeUsize_spec
    {T : Type} (s : Slice T) (r : core_models.ops.range.Range Std.Usize)
    (h0 : r.start.val ≤ r.end.val) (h1 : r.end.val ≤ s.val.length) :
    ⦃ ⌜ True ⌝ ⦄
    core_models.Slice.Insts.Core_modelsOpsIndexIndexMut.index_mut
      (core_models.ops.range.RangeUsize.Insts.Core_modelsSliceIndexSliceIndexSliceSlice T) s r
    ⦃ ⇓ p => ⌜ p.1.val = s.val.slice r.start.val r.end.val ∧
                p.1.val.length = r.end.val - r.start.val ∧
                ∀ s', (p.2 s').val = s.val.setSlice! r.start.val s'.val ⌝ ⦄ := by
  unfold core_models.Slice.Insts.Core_modelsOpsIndexIndexMut.index_mut
         core_models.ops.range.RangeUsize.Insts.Core_modelsSliceIndexSliceIndexSliceSlice
         core_models.cmRangeUsizeToAeneas
         core.slice.index.Slice.index_mut
         core.slice.index.SliceIndexRangeUsizeSlice.index_mut
  have h0' : (⟨r.start, r.end⟩ : core.ops.range.Range Std.Usize).start
              ≤ (⟨r.start, r.end⟩ : core.ops.range.Range Std.Usize).end := by
    simpa [UScalar.le_equiv] using h0
  have h1' : (⟨r.start, r.end⟩ : core.ops.range.Range Std.Usize).end.val ≤ (Slice.length s) := by
    simpa [Slice.length] using h1
  simp only [Triple, WP.wp]
  simp [h0', h1', Slice.length]
  simp [List.slice, List.length_drop, List.length_take]
  omega

/-! ### `core_models.slice.Slice.copy_from_slice` -/

/-- `copy_from_slice dst src` succeeds with the source slice `src`
    whenever both slices have the same length (the impl model returns
    `src` outright when lengths match). -/
@[spec]
theorem core_models_slice_Slice_copy_from_slice_spec
    {T : Type} (cpy : core_models.marker.Copy T) (dst src : Slice T)
    (h : dst.val.length = src.val.length) :
    ⦃ ⌜ True ⌝ ⦄
    core_models.slice.Slice.copy_from_slice cpy dst src
    ⦃ ⇓ r => ⌜ r = src ⌝ ⦄ := by
  unfold core_models.slice.Slice.copy_from_slice
  have h' : dst.len = src.len := by
    apply Std.UScalar.eq_of_val_eq
    simp [h]
  simp [Triple, WP.wp, h']

end libcrux_iot_sha3.Sponge
