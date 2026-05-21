/-
  # Phase 1a — Spec-side scaffolding for `sponge.xor_block_into_state`.

  This file installs the spec-side scaffolding needed to drive the
  **monadic-in-post** posts of `load_block_spec` (and `load_block_full_spec`)
  in `Sponge/Bytes.lean` via `hax_mvcgen`.

  ## Status (Phase 1a closer, 2026-05-21) — Partial-B

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

  **Future work (deferred — see Bytes.lean `Remaining post strength`):**

  - `xor_block_closure_call_mut_spec` — the per-cell `@[spec]` for the
    25-cell `from_fn` body. The proof shell is staged at the bottom of this
    file (see commented doc-block); inner do-chain
    (`slice-index → try_from → unwrap → from_le_bytes → ok`) for the
    `b < rate/8` branch remains to be driven.
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

  **Status (Phase 1a closer, 2026-05-21):**
  Stubbed out — see file-level "Status" doc-comment below.

  The Triple shape is:

  ```
  @[spec] theorem xor_block_closure_call_mut_spec
      (state : Std.Array Std.U64 25#usize) (block : Slice Std.U8)
      (rate : Std.Usize) (k : Std.Usize)
      (h_k : k.val < 25)
      (h_rate : rate.val ≤ 200)
      (h_blk_len : block.val.length = rate.val) :
      ⦃ ⌜ True ⌝ ⦄
      sponge.xor_block_into_state.closure.Insts.Core_modelsOpsFunctionFnMutTupleUsizeU64.call_mut
        (rate, state, block) k
      ⦃ ⇓ r => ⌜ r = (xor_block_value_at state block rate k.val,
                       (rate, state, block)) ⌝ ⦄
  ```

  The proof needs to drive the inner do-chain
  `slice-index → try_from → unwrap → from_le_bytes → ok` in the
  `b < rate/8` branch and produce the bytes-as-LE-u64 equality
  matching `Std.core.num.U64.from_le_bytes (list_8_at block.val (8*b))`.

  Future work — this is the per-cell `@[spec]` consumed by
  `from_fn_pure_spec` to characterize `sponge.xor_block_into_state`. -/

end libcrux_iot_sha3.Sponge
