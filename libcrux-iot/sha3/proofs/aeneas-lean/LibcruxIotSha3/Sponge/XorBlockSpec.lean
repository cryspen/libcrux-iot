/-
  # Phase 1a — Spec-side scaffolding for `sponge.xor_block_into_state`.

  This file installs the spec-side scaffolding needed to drive the
  **monadic-in-post** posts of `load_block_spec` (and `load_block_full_spec`)
  in `Sponge/Bytes.lean` via `hax_mvcgen`.

  ## Status (Phase 1a closer, 2026-05-21) — Partial-B (extended 2026-05-21)

  **Landed:**

  - `from_fn_pure_spec` — generic `@[spec]` analog of `createi_pure_spec`
    (HacspecBridge.lean:663) but stated over the *direct* `FnMut` instance
    (no `Fn` wrapper required). `sponge.xor_block_into_state` uses
    `core_models.array.from_fn` directly with a `FnMut`, not the `Fn`-wrapped
    `createi`. This generic Triple is reusable for any pure FnMut closure.
  - `list_8_at` / `list_8_at_val_eq_slice` — helpers that extract 8 bytes
    from a list at offset `o`, padded to length 8, with a proof that the
    padded form coincides with the exact slice when `o + 8 ≤ length`.
  - `xor_block_value_at` — the per-cell pure value characterizing the
    closure body (`f`-side for `from_fn_pure_spec`).
  - **`xor_block_into_state_closure_call_mut_spec`** (NEW, 2026-05-21
    extended pass): the per-cell `@[spec]` for the 25-cell `from_fn` body.
    Proof drives the inner do-chain manually:
    `div/rem → mul/add → div → if → (slice-index → try_from → unwrap →
    from_le_bytes → lift) | (Array.index_usize)`. In the `b < rate/8`
    branch, matches the constructed 8-byte array's `.val` with
    `list_8_at block.val (8b)` via `list_8_at_val_eq_slice`. Closed under
    only `propext`, `Classical.choice`, `Quot.sound` (no `Lean.ofReduceBool`
    / `Lean.trustCompiler` since no `bv_decide` / `decide` is used).

  **Future work (deferred — see Bytes.lean `Remaining post strength`):**

  - Strengthening `state.load_block_2u32_loop0_spec` /
    `state.load_block_2u32_loop1_spec` invariants to characterize
    `state_flat[j]` / `s'.st[5*(j%5)+j/5]` after iteration.
  - Driving `state.KeccakState.load_block_spec`'s monadic-in-post post via
    `from_fn_pure_spec` + the closure spec.

  ## Closure body (Extraction/Funs.lean:1076-1105)

  Given `c = (rate, state, block)` and cell index `k`:

  ```
  x = k / 5
  y = k % 5
  b = 5*y + x   -- = 5*(k%5) + k/5  (the "byte_lane_idx" inverse)
  if b < rate/8 then
    state[k] ^^^ U64.from_le_bytes(block[8b..8b+8])
  else
    state[k]
  ```

  Both branches return `(value, c)` — the closure state is preserved.
  This is **the** key insight that makes `from_fn_pure_spec` applicable:
  even though the body has an `if`, the closure is pure. The conditional
  lives inside the per-cell `f`-function (`xor_block_value_at`).
-/
import LibcruxIotSha3.Sponge.Interleave
import LibcruxIotSha3.Sponge.SliceSpecs

open Aeneas Aeneas.Std Result Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Sponge

open libcrux_iot_sha3.Equivalence

set_option allowUnsafeReducibility true in
attribute [local irreducible] keccak.keccakf1600 keccak_f.keccak_f

/-! ## A generic `from_fn` pure-closure spec.

Analogous to `createi_pure_spec` (HacspecBridge.lean:663) but takes
a `FnMut` instance directly (no `Fn` wrapper). Required because
`sponge.xor_block_into_state` calls `core_models.array.from_fn` directly
with the `FnMut` instance of its closure. -/

private theorem from_fn_foldlM_pure_aux
    {T F : Type}
    (inst : core_models.ops.function.FnMut F Std.Usize T) (c : F) (f : Nat → T)
    (l : List Nat) (acc : List T)
    (hpure : ∀ k ∈ l,
      inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c)) :
    l.foldlM
      (fun (s : List T × F) (i : Nat) => do
        let (v, f') ← inst.call_mut s.2 ⟨BitVec.ofNat _ i⟩
        Result.ok (s.1 ++ [v], f'))
      (acc, c) = .ok (acc ++ l.map f, c) := by
  induction l generalizing acc with
  | nil =>
      simp only [List.foldlM_nil, List.map_nil, List.append_nil]; rfl
  | cons h t ih =>
      have hh : inst.call_mut c ⟨BitVec.ofNat _ h⟩ = .ok (f h, c) :=
        hpure h List.mem_cons_self
      have ht : ∀ k ∈ t, inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c) :=
        fun k hk => hpure k (List.mem_cons_of_mem _ hk)
      have hih := ih (acc ++ [f h]) ht
      simp only [List.foldlM_cons, hh, bind_tc_ok, List.map_cons]
      rw [hih]
      simp [List.append_assoc]

/-- Lean-level equation for `from_fn` over pure closures. -/
private theorem from_fn_pure_eq
    {T F : Type} (N : Std.Usize)
    (inst : core_models.ops.function.FnMut F Std.Usize T) (c : F) (f : Nat → T)
    (hpure : ∀ k : Nat, k < N.val →
      inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c)) :
    core_models.array.from_fn N inst c =
      .ok ⟨(List.range N.val).map f,
           by simp [List.length_map, List.length_range]⟩ := by
  have hf : ∀ k ∈ List.range N.val,
      inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c) := by
    intro k hk; exact hpure k (List.mem_range.mp hk)
  have h_fold :=
    from_fn_foldlM_pure_aux inst c f (List.range N.val) [] hf
  simp only [List.nil_append] at h_fold
  unfold core_models.array.from_fn rust_primitives.slice.array_from_fn
  split
  · rename_i e heq
    rw [h_fold] at heq; exact absurd heq (by simp)
  · rename_i heq
    rw [h_fold] at heq; exact absurd heq (by simp)
  · rename_i result heq
    rw [h_fold] at heq
    have hres : result = ((List.range N.val).map f, c) :=
      (Result.ok.inj heq).symm
    subst hres
    rfl

/-- **Generic pure-closure `[spec]` for `core_models.array.from_fn`.**

For any closure whose `call_mut` is pure (doesn't mutate state),
`from_fn N inst c` succeeds and its `i`-th cell is `f i`. `hpure` is a
Triple over each `call_mut` so `hax_mvcgen` can recurse through it via
per-closure `@[spec]` lemmas. -/
@[spec]
theorem from_fn_pure_spec
    {T F : Type} [Inhabited T] (N : Std.Usize)
    (inst : core_models.ops.function.FnMut F Std.Usize T) (c : F) (f : Nat → T)
    (hpure : ∀ k : Nat, k < N.val →
      ⦃ ⌜ True ⌝ ⦄
      inst.call_mut c ⟨BitVec.ofNat _ k⟩
      ⦃ ⇓ r => ⌜ r = (f k, c) ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    core_models.array.from_fn N inst c
    ⦃ ⇓ a => ⌜ ∀ i : Nat, i < N.val → a.val[i]! = f i ⌝ ⦄ := by
  have hpure_eq : ∀ k : Nat, k < N.val →
      inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c) :=
    fun k hk => result_eq_of_triple (hpure k hk)
  have heq := from_fn_pure_eq N inst c f hpure_eq
  rw [heq]
  simp only [Triple, WP.wp]
  apply SPred.pure_intro
  intro i hi
  show ((List.range N.val).map f)[i]! = f i
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hi]
  rfl

/-! ## `f`-side per-cell value for `xor_block_into_state.closure`.

The closure body at cell `k` (with `c = (rate, state, block)`) computes
`b := 5*(k%5) + k/5` (the "byte_lane_idx" inverse), then:
- if `b < rate/8`, returns `state[k] ^^^ U64.from_le_bytes(block[8b..8b+8])`;
- otherwise, returns `state[k]`.

We make the function total by using a padded list when the slice access
is out of range. Under the impl precondition `block.val.length = rate.val`
and `rate.val % 8 = 0`, the `b < rate/8` guard implies `8b + 8 ≤ rate.val
= block.val.length`, so the padded case is unreachable. -/

/-- Extract 8 bytes from a list at offset `o`, padded with `0#u8` to length 8.
    Used in `xor_block_value_at` to make the value total. -/
def list_8_at (l : List Std.U8) (o : Nat) : Std.Array Std.U8 8#usize :=
  let raw := (l.drop o).take 8
  let padded := raw ++ List.replicate (8 - raw.length) (0#u8)
  ⟨padded, by
    have h_raw_le : raw.length ≤ 8 := by
      show ((l.drop o).take 8).length ≤ 8
      simp [List.length_take]
    have hlen : padded.length = 8 := by
      show (raw ++ List.replicate (8 - raw.length) (0#u8)).length = 8
      rw [List.length_append, List.length_replicate]
      omega
    simp [hlen]⟩

/-- The padded slice equals an exact slice when the bytes are in range. -/
theorem list_8_at_val_eq_slice
    (l : List Std.U8) (o : Nat) (h : o + 8 ≤ l.length) :
    (list_8_at l o).val = l.slice o (o + 8) := by
  unfold list_8_at
  show ((l.drop o).take 8) ++ List.replicate (8 - ((l.drop o).take 8).length) (0#u8)
        = l.slice o (o + 8)
  have hraw_len : ((l.drop o).take 8).length = 8 := by
    rw [List.length_take, List.length_drop]; omega
  rw [hraw_len]
  simp only [List.replicate, List.append_nil]
  -- `List.slice o (o+8) l = (l.drop o).take 8`
  show (l.drop o).take 8 = l.slice o (o + 8)
  unfold List.slice
  rw [show o + 8 - o = 8 from by omega]

/-- Pure value at cell `k` of `xor_block_into_state`'s closure body. -/
def xor_block_value_at
    (state : Std.Array Std.U64 25#usize) (block : Slice Std.U8) (rate : Std.Usize)
    (k : Nat) : Std.U64 :=
  let b := 5 * (k % 5) + k / 5
  if b < rate.val / 8 then
    state.val[k]! ^^^ Std.core.num.U64.from_le_bytes (list_8_at block.val (8 * b))
  else
    state.val[k]!

/-! ## Purity Triple for `xor_block_into_state.closure.call_mut`.

  Per-cell `@[spec]` consumed by `from_fn_pure_spec` to characterize
  `sponge.xor_block_into_state`. The proof drives the inner do-chain
  `div/rem → mul/add → div → if → (slice-index → try_from → unwrap →
  from_le_bytes → lift) | (index_usize)` and, in the `b < rate/8`
  branch, matches the constructed 8-byte array's `.val` with
  `list_8_at block.val (8b)` via `list_8_at_val_eq_slice`. -/

/-- Local triple-of-ok helper. -/
private theorem triple_of_ok_xbs {α : Type} {x : Result α} {v : α}
    (hx : x = .ok v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ r = v ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp]

/-- Local exist-extractor for Std.Do.Triple-based posts: a Triple
    `⦃True⦄ x ⦃⇓ r => P r⦄` yields `∃ v, x = .ok v ∧ P v`. -/
private theorem triple_exists_ok_xbs {α : Type} {x : Result α}
    {P : α → Prop} (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v =>
      refine ⟨v, rfl, ?_⟩
      have := h; simp [Std.Do.Triple, WP.wp] at this; exact this
  | .fail _ =>
      exfalso; have := h; simp [Std.Do.Triple, WP.wp] at this
  | .div =>
      exfalso; have := h; simp [Std.Do.Triple, WP.wp] at this

/-- Two `Array U8 8` values with equal `.val` produce equal
    `Std.core.num.U64.from_le_bytes` outputs (it factors through `.val`). -/
private theorem U64_from_le_bytes_val_congr
    (a b : Std.Array Std.U8 8#usize) (h : a.val = b.val) :
    Std.core.num.U64.from_le_bytes a = Std.core.num.U64.from_le_bytes b := by
  -- Both sides reduce to the same `BitVec` because they only depend on `.val`.
  -- We use Subtype-eta on UScalar and `.cast` is HEq-friendly.
  have : a = b := Subtype.ext h
  rw [this]

/-- Per-cell purity Triple for `xor_block_into_state.closure.call_mut`. The
    closure tuple is `(rate, state, block)`; the value at cell `k.val`
    is `xor_block_value_at state block rate k.val`. -/
@[spec]
theorem xor_block_into_state_closure_call_mut_spec
    (rate : Std.Usize) (state : Std.Array Std.U64 25#usize)
    (block : Slice Std.U8) (k : Std.Usize)
    (h_k : k.val < 25) (h_rate : rate.val ≤ 200)
    (h_rate_mod : rate.val % 8 = 0)
    (h_blk_len : block.val.length = rate.val) :
    ⦃ ⌜ True ⌝ ⦄
    sponge.xor_block_into_state.closure.Insts.Core_modelsOpsFunctionFnMutTupleUsizeU64.call_mut
      (rate, state, block) k
    ⦃ ⇓ r => ⌜ r = (xor_block_value_at state block rate k.val,
                     (rate, state, block)) ⌝ ⦄ := by
  -- Numeric reductions for the arithmetic prefix:
  --   x = k / 5, y = k % 5, i1 = 5*y, b = i1 + x, i2 = rate / 8.
  -- div: uses div_bv_spec (existential form).
  obtain ⟨x, hx_eq, hx_val, _⟩ :=
    Std.UScalar.div_bv_spec k (y := (5#usize : Std.Usize)) (by decide)
  have hx_val' : x.val = k.val / 5 := by rw [hx_val]; rfl
  obtain ⟨y, hy_eq, hy_val, _⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.rem_bv_spec k (y := (5#usize : Std.Usize)) (by decide))
  have hy_val' : y.val = k.val % 5 := by rw [hy_val]; rfl
  have h_x_lt : x.val < 5 := by rw [hx_val']; omega
  have h_y_lt : y.val < 5 := by rw [hy_val']; exact Nat.mod_lt _ (by decide)
  -- Usize.max ≥ U32.max ≥ 4294967295 ≥ 200 by Usize.bounds_eq.
  have h_max_200 : 200 ≤ Std.Usize.max := by scalar_tac
  -- i1 = 5 * y. We use mul_bv_spec via spec_imp_exists.
  have h_5usize_val : (5#usize : Std.Usize).val = 5 := rfl
  have h_8usize_val : (8#usize : Std.Usize).val = 8 := rfl
  have h_i1_bnd : (5#usize : Std.Usize).val * y.val ≤ Std.UScalar.max .Usize := by
    rw [h_5usize_val, Std.UScalar.max_USize_eq]
    have : 5 * y.val < 25 := by omega
    omega
  obtain ⟨i1, h_i1_eq, h_i1_val_raw, _⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.mul_bv_spec (x := (5#usize : Std.Usize)) (y := y) h_i1_bnd)
  have h_i1_val : i1.val = 5 * y.val := by rw [h_i1_val_raw]; rfl
  have h_i1_lt : i1.val < 25 := by rw [h_i1_val]; omega
  -- b = i1 + x.
  have h_b_bnd : i1.val + x.val ≤ Std.UScalar.max .Usize := by
    rw [Std.UScalar.max_USize_eq]; omega
  obtain ⟨b, h_b_eq, h_b_val_raw, _⟩ :=
    Std.WP.spec_imp_exists (Std.UScalar.add_bv_spec (x := i1) (y := x) h_b_bnd)
  have h_b_val : b.val = 5 * y.val + x.val := by rw [h_b_val_raw, h_i1_val]
  have h_b_alt : b.val = 5 * (k.val % 5) + k.val / 5 := by
    rw [h_b_val, hy_val', hx_val']
  -- i2 = rate / 8.
  obtain ⟨i2, h_i2_eq, h_i2_val_raw, _⟩ :=
    Std.UScalar.div_bv_spec rate (y := (8#usize : Std.Usize)) (by decide)
  have h_i2_val : i2.val = rate.val / 8 := by rw [h_i2_val_raw]; rfl
  -- Unfold the closure body.
  unfold sponge.xor_block_into_state.closure.Insts.Core_modelsOpsFunctionFnMutTupleUsizeU64.call_mut
  -- Reduce arithmetic prefix using triple_of_ok_xbs after computing the .ok-value of the body.
  -- Bound for `index_usize state k`: succeeds since `k.val < 25`.
  have h_state_idx : (Array.index_usize state k : Result Std.U64) = .ok state.val[k.val]! := by
    have hkl : k.val < state.val.length := by
      have hlen : state.val.length = 25 := state.property
      rw [hlen]; exact h_k
    have hkl' : k.val < state.length := by
      show k.val < state.val.length; exact hkl
    have h_state_spec := Std.Array.index_usize_spec state k hkl'
    obtain ⟨v, hv_eq, hv_val⟩ := Std.WP.spec_imp_exists h_state_spec
    rw [hv_eq, hv_val]
  -- Now distinguish on the branch.
  by_cases h_branch : b < i2
  · -- True branch.
    have h_b_lt_rate8 : b.val < rate.val / 8 := by
      have h_lt : b.val < i2.val := (Std.UScalar.lt_equiv b i2).mpr h_branch
      rw [h_i2_val] at h_lt; exact h_lt
    have h_8b_lt : 8 * b.val + 8 ≤ rate.val := by
      have hrate : rate.val = 8 * (rate.val / 8) + rate.val % 8 :=
        (Nat.div_add_mod _ _).symm
      omega
    have h_8b_le_max : 8 * b.val + 8 ≤ Std.Usize.max := by omega
    -- i4 = 8 * b.
    have h_i4_bnd : (8#usize : Std.Usize).val * b.val ≤ Std.UScalar.max .Usize := by
      rw [Std.UScalar.max_USize_eq]
      show 8 * b.val ≤ Std.Usize.max; omega
    obtain ⟨i4, h_i4_eq, h_i4_val_raw, _⟩ :=
      Std.WP.spec_imp_exists
        (Std.UScalar.mul_bv_spec (x := (8#usize : Std.Usize)) (y := b) h_i4_bnd)
    have h_i4_val : i4.val = 8 * b.val := by rw [h_i4_val_raw]; rfl
    -- i5 = i4 + 8.
    have h_i5_bnd : i4.val + (8#usize : Std.Usize).val ≤ Std.UScalar.max .Usize := by
      rw [Std.UScalar.max_USize_eq, h_i4_val]
      show 8 * b.val + 8 ≤ Std.Usize.max; omega
    obtain ⟨i5, h_i5_eq, h_i5_val_raw, _⟩ :=
      Std.WP.spec_imp_exists
        (Std.UScalar.add_bv_spec (x := i4) (y := (8#usize : Std.Usize)) h_i5_bnd)
    have h_i5_val : i5.val = 8 * b.val + 8 := by rw [h_i5_val_raw, h_i4_val]; rfl
    -- Slice index over Range<usize>.
    have h_range_le : i4.val ≤ i5.val := by omega
    have h_range_in_blk : i5.val ≤ block.val.length := by rw [h_blk_len, h_i5_val]; omega
    have h_slice_triple := core_models_Slice_Insts_index_RangeUsize_spec
      (T := Std.U8) block ⟨i4, i5⟩ h_range_le h_range_in_blk
    have h_slice_exists := triple_exists_ok_xbs h_slice_triple
    obtain ⟨s1, h_s1_eq, h_s1_val_eq, h_s1_len⟩ := h_slice_exists
    have h_s1_val_len : s1.val.length = (8#usize : Std.Usize).val := by
      rw [h_s1_len]; show i5.val - i4.val = 8; omega
    -- try_from + unwrap fused.
    have h_try_triple := core_models_array_try_from_slice_spec
      (T := Std.U8) (N := (8#usize : Std.Usize))
      core_models.U8.Insts.Core_modelsMarkerCopy s1 h_s1_val_len
    have h_try_eq :
        core_models.Array.Insts.Core_modelsConvertTryFromShared0SliceTryFromSliceError.try_from
          (8#usize : Std.Usize) core_models.U8.Insts.Core_modelsMarkerCopy s1
        = .ok (.Ok (Std.Array.make 8#usize s1.val (by simp [h_s1_val_len]))) := by
      have h := triple_exists_ok_xbs h_try_triple
      obtain ⟨r, hr_eq, hr_val⟩ := h
      rw [hr_eq, hr_val]
    -- Assemble the body's .ok-equation.
    have h_body_eq :
        sponge.xor_block_into_state.closure.Insts.Core_modelsOpsFunctionFnMutTupleUsizeU64.call_mut
          (rate, state, block) k =
        .ok (xor_block_value_at state block rate k.val, (rate, state, block)) := by
      -- The unfolded body is `do (i,a,s) := c; ...`.
      show (do
        let (i, a, s) := (rate, state, block);
        let x ← k / 5#usize
        let y ← k % 5#usize
        let i1 ← 5#usize * y
        let b ← i1 + x
        let i2 ← i / 8#usize
        if b < i2 then
          let i3 ← Array.index_usize a k
          let i4 ← 8#usize * b
          let i5 ← i4 + 8#usize
          let s1 ← core_models.Slice.Insts.Core_modelsOpsIndexIndex.index
            (core_models.ops.range.RangeUsize.Insts.Core_modelsSliceIndexSliceIndexSliceSlice
              Std.U8) s { start := i4, «end» := i5 }
          let r ← core_models.Array.Insts.Core_modelsConvertTryFromShared0SliceTryFromSliceError.try_from
            8#usize core_models.U8.Insts.Core_modelsMarkerCopy s1
          let a1 ← core_models.result.Result.unwrap
            core_models.array.TryFromSliceError.Insts.Core_modelsFmtDebug r
          let i6 ← core_models.num.U64.from_le_bytes a1
          let i7 ← Std.lift (i3 ^^^ i6)
          ok (i7, (i, a, s))
        else
          let i3 ← Array.index_usize a k
          ok (i3, (i, a, s))) = _
      simp only []
      rw [hx_eq]; simp only [bind_tc_ok]
      rw [hy_eq]; simp only [bind_tc_ok]
      rw [h_i1_eq]; simp only [bind_tc_ok]
      rw [h_b_eq]; simp only [bind_tc_ok]
      rw [h_i2_eq]; simp only [bind_tc_ok]
      rw [if_pos h_branch]
      rw [h_state_idx]; simp only [bind_tc_ok]
      rw [h_i4_eq]; simp only [bind_tc_ok]
      rw [h_i5_eq]; simp only [bind_tc_ok]
      rw [h_s1_eq]; simp only [bind_tc_ok]
      rw [h_try_eq]; simp only [bind_tc_ok]
      -- unwrap of .Ok a = .ok a.
      show (do
          let a1 ← core_models.result.Result.unwrap
            core_models.array.TryFromSliceError.Insts.Core_modelsFmtDebug
            (.Ok (Std.Array.make 8#usize s1.val (by simp [h_s1_val_len])))
          let i6 ← core_models.num.U64.from_le_bytes a1
          let i7 ← Std.lift (state.val[k.val]! ^^^ i6)
          ok (i7, (rate, state, block))) = _
      unfold core_models.result.Result.unwrap; simp only [bind_tc_ok]
      -- from_le_bytes is `pure (Std.core.num.U64.from_le_bytes a)`.
      have h_fle : (core_models.num.U64.from_le_bytes
                      (Std.Array.make 8#usize s1.val (by simp [h_s1_val_len])) : Result Std.U64)
                = .ok (Std.core.num.U64.from_le_bytes
                         (Std.Array.make 8#usize s1.val (by simp [h_s1_val_len]))) := by
        unfold core_models.num.U64.from_le_bytes rust_primitives.arithmetic.from_le_bytes_u64
        rfl
      rw [h_fle]; simp only [bind_tc_ok]
      -- Std.lift x = .ok x.
      show (Std.lift (state.val[k.val]! ^^^
              Std.core.num.U64.from_le_bytes
                (Std.Array.make 8#usize s1.val (by simp [h_s1_val_len])))
              >>= fun i7 => ok (i7, (rate, state, block))) = _
      unfold Std.lift; simp only [bind_tc_ok]
      -- Final value match.
      apply congrArg
      refine Prod.mk.injEq .. |>.mpr ⟨?_, rfl⟩
      unfold xor_block_value_at
      have h_b_val_eq : 5 * (k.val % 5) + k.val / 5 = b.val := h_b_alt.symm
      rw [show (if 5 * (k.val % 5) + k.val / 5 < rate.val / 8 then
                state.val[k.val]! ^^^
                  Std.core.num.U64.from_le_bytes
                    (list_8_at block.val (8 * (5 * (k.val % 5) + k.val / 5)))
              else state.val[k.val]!) =
            (if b.val < rate.val / 8 then
                state.val[k.val]! ^^^
                  Std.core.num.U64.from_le_bytes
                    (list_8_at block.val (8 * b.val))
              else state.val[k.val]!) from by rw [h_b_val_eq]]
      rw [if_pos h_b_lt_rate8]
      apply congrArg (state.val[k.val]! ^^^ ·)
      apply U64_from_le_bytes_val_congr
      show s1.val = (list_8_at block.val (8 * b.val)).val
      rw [list_8_at_val_eq_slice block.val (8 * b.val) (by rw [h_blk_len]; omega)]
      rw [h_s1_val_eq]
      show block.val.slice i4.val i5.val = block.val.slice (8 * b.val) (8 * b.val + 8)
      rw [h_i4_val, h_i5_val]
    exact triple_of_ok_xbs h_body_eq
  · -- False branch.
    have h_b_ge : ¬ b.val < i2.val := fun h_lt =>
      h_branch ((Std.UScalar.lt_equiv b i2).mp h_lt)
    have h_b_ge_rate8 : ¬ b.val < rate.val / 8 := by rw [← h_i2_val]; exact h_b_ge
    have h_body_eq :
        sponge.xor_block_into_state.closure.Insts.Core_modelsOpsFunctionFnMutTupleUsizeU64.call_mut
          (rate, state, block) k =
        .ok (xor_block_value_at state block rate k.val, (rate, state, block)) := by
      show (do
        let (i, a, s) := (rate, state, block);
        let x ← k / 5#usize
        let y ← k % 5#usize
        let i1 ← 5#usize * y
        let b ← i1 + x
        let i2 ← i / 8#usize
        if b < i2 then
          let i3 ← Array.index_usize a k
          let i4 ← 8#usize * b
          let i5 ← i4 + 8#usize
          let s1 ← core_models.Slice.Insts.Core_modelsOpsIndexIndex.index
            (core_models.ops.range.RangeUsize.Insts.Core_modelsSliceIndexSliceIndexSliceSlice
              Std.U8) s { start := i4, «end» := i5 }
          let r ← core_models.Array.Insts.Core_modelsConvertTryFromShared0SliceTryFromSliceError.try_from
            8#usize core_models.U8.Insts.Core_modelsMarkerCopy s1
          let a1 ← core_models.result.Result.unwrap
            core_models.array.TryFromSliceError.Insts.Core_modelsFmtDebug r
          let i6 ← core_models.num.U64.from_le_bytes a1
          let i7 ← Std.lift (i3 ^^^ i6)
          ok (i7, (i, a, s))
        else
          let i3 ← Array.index_usize a k
          ok (i3, (i, a, s))) = _
      simp only []
      rw [hx_eq]; simp only [bind_tc_ok]
      rw [hy_eq]; simp only [bind_tc_ok]
      rw [h_i1_eq]; simp only [bind_tc_ok]
      rw [h_b_eq]; simp only [bind_tc_ok]
      rw [h_i2_eq]; simp only [bind_tc_ok]
      rw [if_neg h_branch]
      rw [h_state_idx]; simp only [bind_tc_ok]
      apply congrArg
      refine Prod.mk.injEq .. |>.mpr ⟨?_, rfl⟩
      unfold xor_block_value_at
      have h_b_val_eq : 5 * (k.val % 5) + k.val / 5 = b.val := h_b_alt.symm
      rw [show (if 5 * (k.val % 5) + k.val / 5 < rate.val / 8 then
                state.val[k.val]! ^^^
                  Std.core.num.U64.from_le_bytes
                    (list_8_at block.val (8 * (5 * (k.val % 5) + k.val / 5)))
              else state.val[k.val]!) =
            (if b.val < rate.val / 8 then
                state.val[k.val]! ^^^
                  Std.core.num.U64.from_le_bytes
                    (list_8_at block.val (8 * b.val))
              else state.val[k.val]!) from by rw [h_b_val_eq]]
      rw [if_neg h_b_ge_rate8]
    exact triple_of_ok_xbs h_body_eq

/-! ## Direct `@[spec]` for `sponge.xor_block_into_state`.

Combines `from_fn_pure_spec` with the per-cell closure spec to give a
direct characterization of each cell of the output array. -/

/-- Direct per-cell spec for `sponge.xor_block_into_state`. Each output
    cell equals `xor_block_value_at state block rate i`. -/
@[spec]
theorem sponge_xor_block_into_state_spec
    (rate : Std.Usize) (state : Std.Array Std.U64 25#usize)
    (block : Slice Std.U8)
    (h_rate : rate.val ≤ 200)
    (h_rate_mod : rate.val % 8 = 0)
    (h_blk_len : block.val.length = rate.val) :
    ⦃ ⌜ True ⌝ ⦄
    sponge.xor_block_into_state state block rate
    ⦃ ⇓ a => ⌜ ∀ i : Nat, i < 25 →
                a.val[i]! = xor_block_value_at state block rate i ⌝ ⦄ := by
  unfold sponge.xor_block_into_state
  -- Apply `from_fn_pure_spec` with `f := xor_block_value_at state block rate`
  -- and `c := (rate, state, block)`.
  apply from_fn_pure_spec
    (f := fun i => xor_block_value_at state block rate i)
    (c := (rate, state, block))
  intro k hk
  -- The per-cell spec uses `⟨BitVec.ofNat _ k⟩ : Std.Usize` as the index;
  -- its `.val` is `k` when `k ≤ Std.Usize.max`.
  have hk25 : k < 25 := by
    show k < (25#usize : Std.Usize).val; exact hk
  have hk_max : k ≤ Std.Usize.max := by
    have : 25 ≤ Std.Usize.max := by scalar_tac
    omega
  -- Cast the closure-call-mut spec to our index form.
  have h_idx_val : (⟨BitVec.ofNat Std.UScalarTy.Usize.numBits k⟩ : Std.Usize).val = k := by
    show (BitVec.ofNat _ k).toNat = k
    simp only [BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    have hmax : Std.Usize.max + 1 = 2 ^ Std.UScalarTy.Usize.numBits := by
      simp [Std.Usize.max, Std.Usize.numBits]
    omega
  have h_call := xor_block_into_state_closure_call_mut_spec
    rate state block ⟨BitVec.ofNat _ k⟩
    (by rw [h_idx_val]; exact hk25) h_rate h_rate_mod h_blk_len
  -- The post `r = (xor_block_value_at state block rate idx.val, c)` becomes
  -- `r = (xor_block_value_at state block rate k, c)` after `h_idx_val`.
  rw [h_idx_val] at h_call
  exact h_call

end libcrux_iot_sha3.Sponge
