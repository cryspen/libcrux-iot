/-
  # Phase 1a — Loop Triples for `load_block` / `store_block` outer fixpoints.

  Provides three `@[spec]` Triples, one per Aeneas `partial_fixpoint` loop,
  threading a `loop_range_spec_usize`-style forward induction:

  - `state.load_block_2u32_loop0_spec`   — outer fixpoint of load-loop 0.
    Body: read 8 bytes from `blocks` at offset `start + 8*i`, interleave,
    write to `state_flat[i]`. ✅ proved (uses `core_models_array_try_from_slice_spec`).
  - `state.load_block_2u32_loop1_spec`   — outer fixpoint of load-loop 1.
    Body: XOR `state_flat[i]` (both halves) into `s.st[5*(i%5) + i/5]`. ✅ proved.
  - `state.store_block_2u32_loop_spec`   — outer fixpoint of store-loop.
    Body: deinterleave `s.st[5*(i%5) + i/5]` and write 8 bytes to
    `out[8*i .. 8*i + 8]`. ✅ proved with slice-length-preservation post.

  Each loop runs over the range `iter.start..iter.end` with step 1.

  ## Strategy

  All three Triples follow the same template: apply
  `loop_range_spec_usize` (`Equivalence/HacspecBridge.lean:231`) with an
  invariant `inv k acc := Q k acc`, where `Q` records what the loop has
  accomplished after `k - iter.start` iterations.

  The most generic statable form for each loop is the
  iterated-body-application form: the result equals `body` applied
  iteratively from the initial accumulator. We expose this as
  `*_iter_post` predicates and state Triples in terms of them.

  Since each loop body itself requires walking ~7-10 sub-Triples (slice
  index/copy/try_from/from_le_bytes/lift/interleave), and those sub-Triples
  introduce a substantial residue of side-conditions on `Slice` length and
  `Range` bounds, the body Triple proof for the load/store loops is
  deferred. The Triples below establish the *shape* of the post via the
  no-information invariant `inv k acc := True`, which gives us trivial
  termination ("loop returns ok") and is the natural staging point: the
  downstream `load_block_spec` / `store_block_spec` then refines the post
  by adding `Q`-clauses on the accumulator as those sub-Triples come in.

  These weak Triples can already be consumed by `hax_mvcgen` to step
  through the surrounding `state.load_block_2u32` / `state.store_block_2u32`
  glue, freeing those proofs from re-proving "the loop terminates".
-/
import LibcruxIotSha3.Sponge.SliceSpecs
import LibcruxIotSha3.Sponge.Interleave

open Aeneas Aeneas.Std Result ControlFlow Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Sponge

open libcrux_iot_sha3.Equivalence

set_option allowUnsafeReducibility true in
attribute [local irreducible] keccak.keccakf1600 keccak_f.keccak_f

/-! ### Local helpers -/

/-- Local copy of the private `triple_of_ok_local` pattern: an `.ok v`
    `Result` satisfies any `Triple` whose post `P r` holds at `v`. -/
private theorem triple_of_ok_local {α : Type} {x : Result α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, hp]

open libcrux_iot_sha3.Equivalence (triple_imp_intro
  loop_range_spec_usize IteratorRange_next_spec_usize
  pure_prop_holds of_pure_prop_holds)

/-! ## Phase 1a prerequisite — loop Triples for load/store partial_fixpoints.

The body of each loop performs a `Range.next` step that *forks* on
whether the iterator is exhausted (`None` -> emit `.done acc`) or has a
next value `i` (`Some i` -> compute the body's effect on the
accumulator, emit `.cont (iter1, acc')`). To bridge the iterator-shaped
`partial_fixpoint` form to a clean `Nat.fold`-style post, we apply
`loop_range_spec_usize` with the *trivial* invariant `inv _ _ := True`.

This produces a Triple of shape

    ⦃ True ⦄ loop body (iter, init) ⦃ ⇓ _ => True ⦄,

i.e. it asserts only that the loop terminates successfully when the
iterator's `start ≤ end`. The strong fold-over-body characterization
required for the full `load_block_spec` / `store_block_spec` will be
derived from this base by the downstream caller (which threads its own
accumulator-tracking invariant). -/

/-! ### Loop 0 of `state.load_block_2u32`.

The body reads two 4-byte windows of `blocks`, decodes each as a `U32`
LE, interleaves them, and writes the result to `state_flat[i]`.

Preconditions:
- `start.val + 8 * iter.end.val ≤ Std.Usize.max` (offset overflow)
- `start.val + 8 * iter.end.val ≤ blocks.val.length`  (slice bound)
- `iter.end.val ≤ 25` (Array.update bound on the 25-cell `state_flat`).

Proof: `loop_range_spec_usize` with a strong invariant that records the
post-`interleave` BV pair at every touched cell.  The body Triple closes
via `mvcgen` once all sub-Triples (`try_from`, `from_le_bytes`,
`Result.unwrap`, slice subindexing, `interleave`) are in scope. -/

/-! Helper definitions for Loop0's strengthened invariant.

After Loop0's k-th iteration, `state_flat[j]` (for `j < k`) is the
post-`interleave` Lane2U32 obtained from the two-`U32` halves recovered
from two 4-byte LE windows from `blocks` at offsets `start+8j` and
`start+8j+4`.  We capture the *pre-interleave* pair in
`Lane2U32_from_4byte_LE_pairs` and then state the post in terms of
`interleave_bv` applied to its two halves (so `interleave_spec`'s
pair-equality on `.bv`s plugs in directly). -/

/-- The `Lane2U32` pre-interleave pair constructed at iteration `j`
    of Loop0: reads two 4-byte LE windows from `blocks` at offsets
    `start+8j` and `start+8j+4`, interpreting each as a `U32`, then
    pairs them.  The body's `Lane2U32.interleave` step is applied to
    this pair to obtain the actual lane stored in `state_flat[j]`. -/
def Lane2U32_from_4byte_LE_pairs
    (blocks : Slice Std.U8) (start : Std.Usize) (j : Nat) : lane.Lane2U32 :=
  let lo_bytes : Std.Array Std.U8 4#usize :=
    ⟨((blocks.val.drop (start.val + 8 * j)).take 4) ++
       List.replicate (4 - ((blocks.val.drop (start.val + 8 * j)).take 4).length) (0#u8),
     by
       have : ((blocks.val.drop (start.val + 8 * j)).take 4).length ≤ 4 := by
         simp [List.length_take]
       have hlen :
           (((blocks.val.drop (start.val + 8 * j)).take 4) ++
             List.replicate (4 - ((blocks.val.drop (start.val + 8 * j)).take 4).length) (0#u8)).length
           = 4 := by
         rw [List.length_append, List.length_replicate]; omega
       simp [hlen]⟩
  let hi_bytes : Std.Array Std.U8 4#usize :=
    ⟨((blocks.val.drop (start.val + 8 * j + 4)).take 4) ++
       List.replicate (4 - ((blocks.val.drop (start.val + 8 * j + 4)).take 4).length) (0#u8),
     by
       have : ((blocks.val.drop (start.val + 8 * j + 4)).take 4).length ≤ 4 := by
         simp [List.length_take]
       have hlen :
           (((blocks.val.drop (start.val + 8 * j + 4)).take 4) ++
             List.replicate (4 - ((blocks.val.drop (start.val + 8 * j + 4)).take 4).length) (0#u8)).length
           = 4 := by
         rw [List.length_append, List.length_replicate]; omega
       simp [hlen]⟩
  Std.Array.make 2#usize
    [Std.core.num.U32.from_le_bytes lo_bytes,
     Std.core.num.U32.from_le_bytes hi_bytes]
    (by simp)

/-- The outer fixpoint of `state.load_block_2u32_loop0` terminates with
    `.ok`, and at every touched index `j ∈ [0, iter.end)` the resulting
    `state_flat[j]` carries the post-`interleave` BV pair derived from
    the two 4-byte LE windows of `blocks` at offsets `start+8j` and
    `start+8j+4`.  Stated in BitVec form so the `interleave_spec`
    output (a pair-equality on `.bv`s) plugs in directly. -/
@[spec]
theorem state.load_block_2u32_loop0_spec
    (iter : core_models.ops.range.Range Std.Usize)
    (blocks : Slice Std.U8) (start : Std.Usize)
    (state_flat : Std.Array lane.Lane2U32 25#usize)
    (h_le : iter.start.val ≤ iter.end.val)
    (h_bnd : iter.end.val ≤ 25)
    (h_off : start.val + 8 * iter.end.val ≤ Std.Usize.max)
    (h_blk : start.val + 8 * iter.end.val ≤ blocks.val.length)
    (h_zero : iter.start.val = 0) :
    ⦃ ⌜ True ⌝ ⦄
    state.load_block_2u32_loop0 iter blocks start state_flat
    ⦃ ⇓ r => ⌜
        ∀ j : Nat, j < iter.end.val → j < 25 →
          ((r.val[j]!).val[0]!.bv, (r.val[j]!).val[1]!.bv)
            = interleave_bv
                ((Lane2U32_from_4byte_LE_pairs blocks start j).val[0]!).bv
                ((Lane2U32_from_4byte_LE_pairs blocks start j).val[1]!).bv
    ⌝ ⦄ := by
  obtain ⟨iter_start, iter_end⟩ := iter
  simp only at h_zero h_le
  unfold state.load_block_2u32_loop0
  -- Strong invariant: at iteration `k`, every touched cell (`j < k`)
  -- carries the post-`interleave` BV pair, and every untouched cell
  -- (`j ≥ k`) equals its initial value in `state_flat`. `h_zero` makes
  -- the `j < k` clause vacuous at `k = iter_start`.
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, s1) => state.load_block_2u32_loop0.body blocks start iter1 s1)
      state_flat iter_start iter_end
      (fun k s' => pure (
          (∀ j : Nat, j < k.val → j < 25 →
              ((s'.val[j]!).val[0]!.bv, (s'.val[j]!).val[1]!.bv)
                = interleave_bv
                    ((Lane2U32_from_4byte_LE_pairs blocks start j).val[0]!).bv
                    ((Lane2U32_from_4byte_LE_pairs blocks start j).val[1]!).bv)
          ∧ (∀ j : Nat, k.val ≤ j → j < 25 →
                s'.val[j]! = state_flat.val[j]!)))
      h_le
      (pure_prop_holds ⟨
        fun j hjk _ => by
          rw [h_zero] at hjk; exact absurd hjk (Nat.not_lt_zero j),
        fun _ _ _ => rfl⟩)
      ?_)
  · rw [PostCond.entails_noThrow]
    intro r h
    obtain ⟨h_done, _h_undone⟩ := of_pure_prop_holds h
    intro j hj_end hj_25
    exact h_done j hj_end hj_25
  · intro acc k h_ge h_le_k hinv
    obtain ⟨h_acc_done, h_acc_undone⟩ := of_pure_prop_holds hinv
    unfold state.load_block_2u32_loop0.body
    apply Std.Do.Triple.bind _ _
      (IteratorRange_next_spec_usize k iter_end
        (Q := PostCond.noThrow fun (oi : Option Std.Usize × _) => ⌜
          match oi.1 with
          | none => k.val ≥ iter_end.val ∧
                    oi.2 = { start := k, «end» := iter_end }
          | some i => i = k ∧ k.val < iter_end.val ∧
                      oi.2.«end» = iter_end ∧ oi.2.start.val = k.val + 1
        ⌝)
        (fun hlt s' hs' => by
          dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
          exact ⟨rfl, hlt, rfl, hs'⟩)
        (fun hge => by
          dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
          exact ⟨hge, rfl⟩))
    intro ⟨o, iter1⟩
    apply triple_imp_intro
    rcases o with _ | i
    · rintro ⟨hge, hiter1_eq⟩
      show ⦃⌜True⌝⦄ (Aeneas.Std.Result.ok (done acc) : Result _) ⦃_⦄
      -- Loop-exhaustion branch: `k = iter_end`, so the inv's `j < k`
      -- clause already gives the post.
      have hk_eq : k.val = iter_end.val := Nat.le_antisymm h_le_k hge
      refine triple_of_ok_local rfl (pure_prop_holds ⟨?_, ?_⟩)
      · intro j hj_end hj_25
        exact h_acc_done j (hk_eq ▸ hj_end) hj_25
      · intro j hj_ge hj_25
        exact h_acc_undone j (hk_eq ▸ hj_ge) hj_25
    · rintro ⟨hi_eq, hk_lt, hiter1_end, hiter1_start⟩
      cases hi_eq
      have hk_25 : k.val < 25 := by
        have h1 : k.val < iter_end.val := hk_lt
        have h2 : iter_end.val ≤ 25 := h_bnd
        omega
      -- Slice/range bounds for the two 4-byte reads (offsets from `start`).
      -- All omega calls below need explicit `h_blk`/`h_off` to thread through.
      have h_off1 : start.val + 8 * k.val + 4 ≤ blocks.val.length := by
        have h1 : 8 * k.val + 8 ≤ 8 * iter_end.val := by omega
        have h2 : start.val + 8 * iter_end.val ≤ blocks.val.length := h_blk
        omega
      have h_off2 : start.val + 8 * k.val + 8 ≤ blocks.val.length := by
        have h1 : 8 * k.val + 8 ≤ 8 * iter_end.val := by omega
        have h2 : start.val + 8 * iter_end.val ≤ blocks.val.length := h_blk
        omega
      have h_smax1 : start.val + 8 * k.val + 4 ≤ Std.Usize.max := by
        have h1 : 8 * k.val + 8 ≤ 8 * iter_end.val := by omega
        have h2 : start.val + 8 * iter_end.val ≤ Std.Usize.max := h_off
        omega
      have h_smax2 : start.val + 8 * k.val + 8 ≤ Std.Usize.max := by
        have h1 : 8 * k.val + 8 ≤ 8 * iter_end.val := by omega
        have h2 : start.val + 8 * iter_end.val ≤ Std.Usize.max := h_off
        omega
      -- Unfold the trivial `from`-converter (it's `do ok value`); mvcgen
      -- needs it inlined to step into `Lane2U32.interleave`.
      unfold lane.Lane2U32.Insts.Core_modelsConvertFromArrayU322.from
      -- The body's two `try_from + Result.unwrap` chains are tricky for
      -- mvcgen (it picks the wrong unification witness for `Result.unwrap`'s
      -- `v` argument). We pre-reduce both pairs to plain `Array.make`'s
      -- before mvcgen. The slice argument's `.val` to `try_from` is
      -- characterized by `core_models_Slice_Insts_index_RangeUsize_spec`,
      -- so we first walk the slice index Triples to get those `.val`s.
      mvcgen
      -- Remaining VCs:
      -- (a) Scalar bounds — close via `scalar_tac`.
      -- (b) For each `Result.unwrap` VC `r✝ = .Ok r✝ᵢ`: we have hypotheses
      --     `r✝ = .Ok (Array.make 4 _ ⋯)` and `r✝ᵢ = Array.make 4 _ ⋯`.
      --     The right `r✝ᵢ` comes from the *immediately preceding* unwrap
      --     in the chain; we substitute via the array-equation.
      -- (c) ONE strong-invariant preservation VC — handled separately
      --     after `try`-closing the structural VCs.
      all_goals (try (first
        | scalar_tac
        | -- The `Inhabited (Std.Array U8 4#usize)` instance comes from
          -- `core_models_array_try_from_slice_spec`'s param chain; we
          -- pick a canonical witness explicitly.
          exact ⟨Std.Array.make 4#usize (List.replicate 4 0#u8) (by simp)⟩
        | (-- For each `Result.unwrap` VC: provide `∃ v, r = .Ok v` —
           -- the witness comes from the matching `try_from` hypothesis
           -- (`r = .Ok (Array.make ...)`), available as `h_4` / `h_9` etc.
           expose_names
           first
             | exact ⟨_, h_4⟩
             | exact ⟨_, h_9⟩)))
      -- Remaining: the strong-invariant preservation VC. The body's
      -- final step is `Array.update state_flat k lu1`; we expose names
      -- and case-split on j < k vs j = k.
      expose_names
      refine ⟨hk_lt, hiter1_end, hiter1_start, ?_⟩
      apply pure_prop_holds
      -- Goal: ∀ j < iter1.start, ((r_13[j]!)[0]!.bv, (r_13[j]!)[1]!.bv) =
      --         interleave_bv ((Lane2U32_from_4byte_LE_pairs ... j)[0]!.bv)
      --                       ((Lane2U32_from_4byte_LE_pairs ... j)[1]!.bv)
      -- AND ∀ j ≥ iter1.start, r_13[j]! = state_flat[j]!
      -- where r_13 = acc.set k r_12 and h_12 gives the BV pair of r_12.
      have h_r13_acc_length : acc.val.length = 25 := by
        rw [Aeneas.Std.Array.length_eq]; rfl
      refine ⟨?_, ?_⟩
      · -- j < iter1.start → ...
        intro j hj_start hj_25
        have hj_le_k : j ≤ k.val := by
          have : j < k.val + 1 := by rw [← hiter1_start]; exact hj_start
          scalar_tac
        rcases Nat.lt_or_eq_of_le hj_le_k with hj_lt_k | hj_eq_k
        · -- j < k: unchanged by the set.
          have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
          have h_set_ne : (r_13.val)[j]! = (acc.val)[j]! := by
            have : (r_13)[j]! = (acc)[j]! := by
              rw [h_13]
              exact Aeneas.Std.Array.getElem!_Nat_set_ne _ _ _ _ h_ne
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using this
          rw [h_set_ne]
          exact h_acc_done j hj_lt_k hj_25
        · -- j = k: the new lane is r_12, whose BV pair is given by h_12.
          subst hj_eq_k
          have h_lt_acc : k.val < acc.val.length := by rw [h_r13_acc_length]; exact hk_25
          have h_set_eq : (r_13.val)[k.val]! = r_12 := by
            have : (r_13)[k.val]! = r_12 := by
              rw [h_13]
              exact Aeneas.Std.Array.getElem!_Nat_set_eq _ _ _ _ ⟨rfl, h_lt_acc⟩
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using this
          rw [h_set_eq]
          -- Now: ((r_12)[0]!.bv, (r_12)[1]!.bv) =
          --      interleave_bv ((Lane2U32_from_4byte_LE_pairs ... k.val)[0]!.bv)
          --                    ((Lane2U32_from_4byte_LE_pairs ... k.val)[1]!.bv)
          -- h_12 gives: ((r_12)[0]!.bv, (r_12)[1]!.bv) =
          --             interleave_bv ((Array.make 2 [r_6, r_11])[0]!.bv)
          --                           ((Array.make 2 [r_6, r_11])[1]!.bv)
          -- So it remains to show the helper's halves match r_6/r_11.
          rw [h_12]
          -- Reduce both sides' `Array.make 2 [_, _]` `.val[i]!` projections.
          have h_make0 :
              ((Std.Array.make 2#usize [r_6, r_11] (by simp)
                  : lane.Lane2U32).val[0]!) = r_6 := by
            simp [Aeneas.Std.Array.make]
          have h_make1 :
              ((Std.Array.make 2#usize [r_6, r_11] (by simp)
                  : lane.Lane2U32).val[1]!) = r_11 := by
            simp [Aeneas.Std.Array.make]
          rw [h_make0, h_make1]
          -- Now show r_6 = U32.from_le_bytes lo_bytes(helper) and
          -- r_11 = U32.from_le_bytes hi_bytes(helper).
          -- h_6: r_6 = from_le_bytes r_5  where r_5 = Array.make 4 r_3 (h_5)
          -- and h_3: r_3.val = List.slice r_1 r_2 blocks ∧ length = r_2 - r_1.
          -- The helper's lo_bytes = Array.make 4 ((blocks.drop (start+8k)).take 4 ++ pad).
          -- We need r_5 = helper's lo_bytes (as Array U8 4).
          -- Auxiliary scalar identities:
          have h_r : r.val = 8 * k.val := by scalar_tac
          have h_r1 : r_1.val = start.val + 8 * k.val := by scalar_tac
          have h_r2 : r_2.val = start.val + 8 * k.val + 4 := by scalar_tac
          have h_r7 : r_7.val = start.val + 8 * k.val + 8 := by scalar_tac
          -- Length of the take-4 slice from blocks:
          have h_len_lo : ((blocks.val.drop (start.val + 8 * k.val)).take 4).length = 4 := by
            rw [List.length_take, List.length_drop]; omega
          have h_len_hi :
              ((blocks.val.drop (start.val + 8 * k.val + 4)).take 4).length = 4 := by
            rw [List.length_take, List.length_drop]; omega
          -- r_3.val unfolded to a take-form:
          have h_r3_val : r_3.val = (blocks.val.drop (start.val + 8 * k.val)).take 4 := by
            have := h_3.1
            unfold List.slice at this
            rw [h_r1, h_r2] at this
            rw [show start.val + 8 * k.val + 4 - (start.val + 8 * k.val) = 4 from by omega] at this
            exact this
          have h_r8_val : r_8.val = (blocks.val.drop (start.val + 8 * k.val + 4)).take 4 := by
            have := h_8.1
            unfold List.slice at this
            rw [h_r2, h_r7] at this
            rw [show start.val + 8 * k.val + 8 - (start.val + 8 * k.val + 4) = 4 from by omega] at this
            exact this
          -- Reduce both Array.make 4 _ to equal forms.
          -- r_5 is `Array.make 4 r_3.val` (from h_4 vs h_5 of the unwrap chain).
          have h_r5_val : r_5.val =
              ((blocks.val.drop (start.val + 8 * k.val)).take 4)
              ++ List.replicate
                  (4 - ((blocks.val.drop (start.val + 8 * k.val)).take 4).length) (0#u8) := by
            have h_45 := h_5.symm.trans h_4
            have h_r5_eq : r_5 = Std.Array.make 4#usize r_3.val (by rw [h_3.2]; scalar_tac) :=
              core_models.result.Result.Ok.inj h_45
            rw [h_r5_eq]
            -- (Array.make 4 r_3.val _).val = r_3.val by defn
            show r_3.val = _
            rw [h_r3_val, h_len_lo]
            simp
          have h_r10_val : r_10.val =
              ((blocks.val.drop (start.val + 8 * k.val + 4)).take 4)
              ++ List.replicate
                  (4 - ((blocks.val.drop (start.val + 8 * k.val + 4)).take 4).length) (0#u8) := by
            have h_910 := h_10.symm.trans h_9
            have h_r10_eq : r_10 = Std.Array.make 4#usize r_8.val (by rw [h_8.2]; scalar_tac) :=
              core_models.result.Result.Ok.inj h_910
            rw [h_r10_eq]
            show r_8.val = _
            rw [h_r8_val, h_len_hi]
            simp
          -- Now show the helper's lo_bytes/hi_bytes equal r_5/r_10 (as Std.Array U8 4).
          have h_helper_lo :
              (Lane2U32_from_4byte_LE_pairs blocks start k.val).val[0]! = r_6 := by
            unfold Lane2U32_from_4byte_LE_pairs
            -- The def's Std.Array.make 2 [from_le_bytes lo_bytes, from_le_bytes hi_bytes]
            -- has val[0]! = from_le_bytes lo_bytes.
            simp only [Aeneas.Std.Array.make, List.getElem!_cons_zero]
            rw [h_6]
            -- Goal: from_le_bytes lo_bytes_helper = from_le_bytes r_5
            congr 1
            apply Subtype.ext
            show _ = r_5.val
            rw [h_r5_val]
          have h_helper_hi :
              (Lane2U32_from_4byte_LE_pairs blocks start k.val).val[1]! = r_11 := by
            unfold Lane2U32_from_4byte_LE_pairs
            simp only [Aeneas.Std.Array.make, List.getElem!_cons_succ, List.getElem!_cons_zero]
            rw [h_11]
            congr 1
            apply Subtype.ext
            show _ = r_10.val
            rw [h_r10_val]
          rw [h_helper_lo, h_helper_hi]
      · -- j ≥ iter1.start → r_13[j]! = state_flat[j]!.
        intro j hj_ge hj_25
        have hj_gt_k : k.val < j := by
          have : k.val + 1 ≤ j := by rw [← hiter1_start]; exact hj_ge
          scalar_tac
        have h_ne : k.val ≠ j := Nat.ne_of_lt hj_gt_k
        have h_set_ne : (r_13.val)[j]! = (acc.val)[j]! := by
          have : (r_13)[j]! = (acc)[j]! := by
            rw [h_13]
            exact Aeneas.Std.Array.getElem!_Nat_set_ne _ _ _ _ h_ne
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using this
        rw [h_set_ne]
        exact h_acc_undone j (Nat.le_of_lt hj_gt_k) hj_25

/-! ### Loop 1 of `state.load_block_2u32`. -/

/-! Helper definitions for Loop1's strengthened invariant.

After Loop1's k-th iteration the touched lanes (at impl-flat-index
`5*(j%5) + j/5` for `j < k`) carry a XOR-of-halves formula, while the
untouched lanes preserve their initial values. We name these as `def`s
so the loop's `inv` is fold-form (per SKILL §8.2 no inline computation
in posts). -/

/-- The lane-XOR value at impl-flat-index `5*(j%5) + j/5` produced by
    one iteration of Loop1 at iteration `j`. Encoded as a `BitVec 64`
    via `lift_lane_bv`. -/
def loop1_lane_at
    (s : state.KeccakState) (state_flat : Std.Array lane.Lane2U32 25#usize)
    (j : Nat) : BitVec 64 :=
  let p := 5 * (j % 5) + j / 5
  let s_lane := s.st.val[p]!
  lift_lane_bv
    ((s_lane.val[0]!).bv ^^^ (state_flat.val[j]!.val[0]!).bv)
    ((s_lane.val[1]!).bv ^^^ (state_flat.val[j]!.val[1]!).bv)

/-- The outer fixpoint of `state.load_block_2u32_loop1` terminates with
    `.ok`, provided `iter.start.val ≤ iter.end.val ≤ 25`.

    Per-iteration: at index `i ∈ [iter.start, iter.end)`, XOR the two
    halves of `state_flat[i]` into the lane `s.st[5*(i%5) + i/5]`.

    Note the lane index `5*(i%5) + i/5` is bounded by 25 when `i < 25`,
    so the inner `state.KeccakState.set_lane` / `get_lane` calls succeed.
    We propagate the bound `iter.end.val ≤ 25` to discharge those bounds.

    Proof: `loop_range_spec_usize` with `inv k acc := acc.i = s.i`. The
    body only calls `set_lane` which is `{ self with st := a }`, preserving
    the `i` field. -/
@[spec]
theorem state.load_block_2u32_loop1_spec
    (iter : core_models.ops.range.Range Std.Usize)
    (state_flat : Std.Array lane.Lane2U32 25#usize)
    (s : state.KeccakState)
    (h_le : iter.start.val ≤ iter.end.val)
    (h_bnd : iter.end.val ≤ 25)
    (h_zero : iter.start.val = 0) :
    ⦃ ⌜ True ⌝ ⦄
    state.load_block_2u32_loop1 iter s state_flat
    ⦃ ⇓ r => ⌜
        r.i = s.i
        ∧ (∀ j : Nat, j < iter.end.val → j < 25 →
             lift_lane_bv (r.st.val[5*(j%5) + j/5]!).val[0]!.bv
                          (r.st.val[5*(j%5) + j/5]!).val[1]!.bv
             = loop1_lane_at s state_flat j)
    ⌝ ⦄ := by
  obtain ⟨iter_start, iter_end⟩ := iter
  simp only at h_zero h_le
  unfold state.load_block_2u32_loop1
  -- Strong invariant: at iteration `k`, `acc.i = s.i`, every touched
  -- lane (`j < k`) carries the XOR'd `loop1_lane_at s state_flat j`
  -- value, and every untouched lane (`j ≥ k`) equals its initial value
  -- in `s.st`. We track both pieces of information to thread the
  -- preservation step. The `h_zero : iter.start.val = 0` hypothesis
  -- ensures the initial `j < k.val` clause is vacuous.
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, s1) => state.load_block_2u32_loop1.body state_flat iter1 s1)
      s iter_start iter_end
      (fun k s' => pure (
          s'.i = s.i
          ∧ (∀ j : Nat, j < k.val → j < 25 →
               lift_lane_bv (s'.st.val[5*(j%5) + j/5]!).val[0]!.bv
                            (s'.st.val[5*(j%5) + j/5]!).val[1]!.bv
               = loop1_lane_at s state_flat j)
          ∧ (∀ j : Nat, k.val ≤ j → j < 25 →
               s'.st.val[5*(j%5) + j/5]! = s.st.val[5*(j%5) + j/5]!)))
      h_le
      (pure_prop_holds ⟨rfl,
        fun j hjk _ => by
          -- `j < iter_start.val = 0` is impossible.
          rw [h_zero] at hjk; exact absurd hjk (Nat.not_lt_zero j),
        fun _ _ _ => rfl⟩)
      ?_)
  · rw [PostCond.entails_noThrow]
    intro r h
    obtain ⟨hri, hri_lanes, _hri_unchanged⟩ := of_pure_prop_holds h
    refine ⟨hri, ?_⟩
    intro j hj_end hj_25
    exact hri_lanes j hj_end hj_25
  · intro acc k h_ge h_le_k hinv
    obtain ⟨h_acc_i, h_acc_done, h_acc_undone⟩ := of_pure_prop_holds hinv
    unfold state.load_block_2u32_loop1.body
    apply Std.Do.Triple.bind _ _
      (IteratorRange_next_spec_usize k iter_end
        (Q := PostCond.noThrow fun (oi : Option Std.Usize × _) => ⌜
          match oi.1 with
          | none => k.val ≥ iter_end.val ∧
                    oi.2 = { start := k, «end» := iter_end }
          | some i => i = k ∧ k.val < iter_end.val ∧
                      oi.2.«end» = iter_end ∧ oi.2.start.val = k.val + 1
        ⌝)
        (fun hlt s' hs' => by
          dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
          exact ⟨rfl, hlt, rfl, hs'⟩)
        (fun hge => by
          dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
          exact ⟨hge, rfl⟩))
    intro ⟨o, iter1⟩
    apply triple_imp_intro
    rcases o with _ | i
    · rintro ⟨hge, hiter1_eq⟩
      show ⦃⌜True⌝⦄ (Aeneas.Std.Result.ok (done acc) : Result _) ⦃_⦄
      -- We have `k ≥ iter_end` in the loop-exhaustion branch and
      -- `k ≤ iter_end` from `loop_range_spec_usize`, so `k = iter_end`.
      -- The inv's `j < k` clause then weakens to `j < iter_end`, and
      -- the `k ≤ j` clause weakens to `iter_end ≤ j`.
      have hk_eq : k.val = iter_end.val := Nat.le_antisymm h_le_k hge
      refine triple_of_ok_local rfl (pure_prop_holds
        ⟨h_acc_i, ?_, ?_⟩)
      · intro j hj_end hj_25
        exact h_acc_done j (Nat.lt_of_lt_of_le hj_end hge) hj_25
      · intro j hj_ge hj_25
        exact h_acc_undone j (hk_eq ▸ hj_ge) hj_25
    · rintro ⟨hi_eq, hk_lt, hiter1_end, hiter1_start⟩
      cases hi_eq
      have hk_25 : k.val < 25 := by
        have h1 : k.val < iter_end.val := hk_lt
        have h2 : iter_end.val ≤ 25 := h_bnd
        omega
      have hk_div : k.val / 5 < 5 := by omega
      have hk_mod : k.val % 5 < 5 := Nat.mod_lt _ (by decide)
      unfold state.KeccakState.get_lane state.KeccakState.set_lane
             lane.Lane2U32.Insts.Core_modelsOpsIndexIndexUsizeU32.index
             lane.Lane2U32.from_ints
      mvcgen
      -- All scalar-bound VCs close via `scalar_tac`. The remaining VC
      -- is the inv-preservation goal: we expose names and discharge it
      -- below.
      all_goals (try scalar_tac)
      expose_names
      -- Goal shape: `k.val < iter_end.val ∧ iter1.end = iter_end ∧
      --   iter1.start.val = k.val + 1 ∧ (pure (... new state inv)).holds`.
      refine ⟨hk_lt, hiter1_end, hiter1_start, ?_⟩
      apply pure_prop_holds
      -- The new state's `.st` is `r_12 = acc.st.set r_11 (Array.make ...)`
      -- where `r_11.val = 5*(k%5) + k/5`. Other than that one cell, the
      -- array agrees with `acc.st`.
      expose_names
      -- Auxiliary scalar identities for the set index.
      have hr_idx : r_11.val = 5 * (k.val % 5) + k.val / 5 := by
        scalar_tac
      have hr_3_idx : r_3.val = 5 * (k.val % 5) + k.val / 5 := by
        scalar_tac
      have hr_idx_25 : r_11.val < 25 := by
        rw [hr_idx]; scalar_tac
      -- Cell-index injectivity on [0, 25): the map j ↦ 5*(j%5)+j/5 is
      -- injective. We package this as a small named hypothesis, proved
      -- by `decide` on the bounded statement.
      have h_inj_dec :
          ∀ (a b : Fin 25), a ≠ b →
            5 * (a.val % 5) + a.val / 5 ≠ 5 * (b.val % 5) + b.val / 5 := by
        decide
      have h_inj : ∀ (j : Nat), j < 25 → j ≠ k.val →
          5 * (j % 5) + j / 5 ≠ 5 * (k.val % 5) + k.val / 5 := by
        intro j hj_25 hjk_ne
        have h_a : (⟨j, hj_25⟩ : Fin 25) ≠ ⟨k.val, hk_25⟩ := by
          intro h; apply hjk_ne; exact Fin.mk.inj_iff.mp h
        exact h_inj_dec ⟨j, hj_25⟩ ⟨k.val, hk_25⟩ h_a
      refine ⟨h_acc_i, ?_, ?_⟩
      · -- ∀ j < k+1, j < 25 → lift_lane_bv (r_12[...][0]!.bv) (r_12[...][1]!.bv) = loop1_lane_at s state_flat j
        intro j hj_start hj_25
        have hj_le_k : j ≤ k.val := by
          have : j < k.val + 1 := by rw [← hiter1_start]; exact hj_start
          scalar_tac
        have hp_lt_25 : 5 * (j % 5) + j / 5 < 25 := by
          have h1 : j % 5 < 5 := Nat.mod_lt _ (by decide)
          have h2 : j / 5 < 5 :=
            (Nat.div_lt_iff_lt_mul (by decide : 0 < 5)).mpr (by scalar_tac)
          scalar_tac
        rcases Nat.lt_or_eq_of_le hj_le_k with hj_lt_k | hj_eq_k
        · -- j < k: lane unchanged by the set since `5*(j%5)+j/5 ≠ r_11.val`.
          have hjk_ne : j ≠ k.val := Nat.ne_of_lt hj_lt_k
          have h_pq_ne :
              5 * (j % 5) + j / 5 ≠ 5 * (k.val % 5) + k.val / 5 :=
            h_inj j hj_25 hjk_ne
          have h_ne : r_11.val ≠ 5 * (j % 5) + j / 5 := by
            rw [hr_idx]; exact (Ne.symm h_pq_ne)
          -- The Std.Array `set/getElem!` lemmas apply directly.
          have h_set_ne :
              (r_12.val)[5 * (j % 5) + j / 5]!
                = (acc.st.val)[5 * (j % 5) + j / 5]! := by
            have : (r_12)[5 * (j % 5) + j / 5]! = (acc.st)[5 * (j % 5) + j / 5]! := by
              rw [h_12]
              exact Aeneas.Std.Array.getElem!_Nat_set_ne _ _ _ _ h_ne
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using this
          rw [h_set_ne]
          exact h_acc_done j hj_lt_k hj_25
        · -- j = k: the lane is the newly written `Array.make 2 [r_5^^^r_7, r_8^^^r_9]`.
          subst hj_eq_k
          have h_lt_acc : 5 * (k.val % 5) + k.val / 5 < acc.st.length := by
            show 5 * (k.val % 5) + k.val / 5 < acc.st.val.length
            rw [Aeneas.Std.Array.length_eq]
            scalar_tac
          have h_set_eq :
              (r_12.val)[5 * (k.val % 5) + k.val / 5]!
                = (Array.make 2#usize [r_5 ^^^ r_7, r_8 ^^^ r_9] (by simp)
                    : lane.Lane2U32) := by
            have : (r_12)[5 * (k.val % 5) + k.val / 5]!
                = (Array.make 2#usize [r_5 ^^^ r_7, r_8 ^^^ r_9] (by simp)
                    : lane.Lane2U32) := by
              rw [h_12]
              exact Aeneas.Std.Array.getElem!_Nat_set_eq _ _ _ _
                ⟨hr_idx, h_lt_acc⟩
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using this
          rw [h_set_eq]
          -- The new lane's halves: val[0]! = r_5 ^^^ r_7, val[1]! = r_8 ^^^ r_9.
          -- The Array.make construction has its .val as the explicit list.
          have h_make_v0 :
              ((Array.make 2#usize [r_5 ^^^ r_7, r_8 ^^^ r_9] (by simp)
                  : lane.Lane2U32).val[0]!) = r_5 ^^^ r_7 := by
            simp [Aeneas.Std.Array.make]
          have h_make_v1 :
              ((Array.make 2#usize [r_5 ^^^ r_7, r_8 ^^^ r_9] (by simp)
                  : lane.Lane2U32).val[1]!) = r_8 ^^^ r_9 := by
            simp [Aeneas.Std.Array.make]
          rw [h_make_v0, h_make_v1]
          -- r_5 = acc.st[r_3][0]!, r_7 = state_flat[k][0]!, etc.
          -- And acc.st[r_3.val]! = s.st[5*(k%5)+k/5]! via h_acc_undone (k ≤ k).
          have h_acc_lane :
              (acc.st.val)[5 * (k.val % 5) + k.val / 5]!
                = (s.st.val)[5 * (k.val % 5) + k.val / 5]! :=
            h_acc_undone k.val (Nat.le_refl _) hk_25
          have h_r4 : r_4 = (s.st.val)[5 * (k.val % 5) + k.val / 5]! := by
            rw [h_4]
            show (acc.st.val)[r_3.val]! = (s.st.val)[5 * (k.val % 5) + k.val / 5]!
            rw [hr_3_idx, h_acc_lane]
          have h_r5 : r_5.bv =
              ((s.st.val)[5 * (k.val % 5) + k.val / 5]!).val[0]!.bv := by
            rw [h_5, h_r4]
            rfl
          have h_r8 : r_8.bv =
              ((s.st.val)[5 * (k.val % 5) + k.val / 5]!).val[1]!.bv := by
            rw [h_8, h_r4]
            rfl
          have h_r6 : r_6 = state_flat.val[k.val]! := by
            rw [h_6]
          have h_r7 : r_7.bv = (state_flat.val[k.val]!).val[0]!.bv := by
            rw [h_7, h_r6]
            rfl
          have h_r9 : r_9.bv = (state_flat.val[k.val]!).val[1]!.bv := by
            rw [h_9, h_r6]
            rfl
          -- Unfold loop1_lane_at and use Std.U32 xor's .bv = xor of .bv.
          unfold loop1_lane_at
          simp only [Aeneas.Std.UScalar.bv_xor, h_r5, h_r7, h_r8, h_r9]
      · -- ∀ j, k+1 ≤ j → j < 25 → r_12[5*(j%5)+j/5]! = s.st[5*(j%5)+j/5]!
        intro j hj_ge hj_25
        have hj_gt_k : k.val < j := by
          have : k.val + 1 ≤ j := by rw [← hiter1_start]; exact hj_ge
          scalar_tac
        have hjk_ne : j ≠ k.val := (Nat.ne_of_lt hj_gt_k).symm
        have h_pq_ne :
            5 * (j % 5) + j / 5 ≠ 5 * (k.val % 5) + k.val / 5 :=
          h_inj j hj_25 hjk_ne
        have h_ne : r_11.val ≠ 5 * (j % 5) + j / 5 := by
          rw [hr_idx]; exact (Ne.symm h_pq_ne)
        have h_set_ne :
            (r_12.val)[5 * (j % 5) + j / 5]!
              = (acc.st.val)[5 * (j % 5) + j / 5]! := by
          have : (r_12)[5 * (j % 5) + j / 5]! = (acc.st)[5 * (j % 5) + j / 5]! := by
            rw [h_12]
            exact Aeneas.Std.Array.getElem!_Nat_set_ne _ _ _ _ h_ne
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using this
        rw [h_set_ne]
        exact h_acc_undone j (Nat.le_of_lt hj_gt_k) hj_25

/-! ### Loop of `state.store_block_2u32`.

The body reads `s.st[5*(i%5) + i/5]`, deinterleaves it, writes two
4-byte halves to `out[8i .. 8i+8]`. After mvcgen, three residual
`(setSlice! ...).length = 4` subgoals remain; these dispatch by
`List.length_setSlice!` + `List.length_slice` + omega (no `simp_all`). -/

/-! Helper definition for the store loop's strengthened invariant.

After Loop's k-th iteration, for each byte index `b ∈ [0, 8k)`:
`out1.val[b]! = ((lift s).val[5*((b/8)%5) + (b/8)/5]!).bv.toLEBytes[b%8]!`.

The `store_block_byte_at` def captures the RHS in fold-form so the
invariant can be stated without inline if/let/conditional in posts
(per SKILL §8.2). -/

/-- The byte produced at position `b` of the store output: takes byte
    `b % 8` of the LE-byte split of the impl-lane at impl-flat-index
    `5*((b/8)%5) + (b/8)/5`, in its `lift`-recovered `U64` form. -/
def store_block_byte_at
    (s : state.KeccakState) (b : Nat) : Std.U8 :=
  let p := 5 * ((b / 8) % 5) + (b / 8) / 5
  let u64 : Std.U64 := lift_lane (s.st.val[p]!)
  -- Take byte `b % 8` (LE) from the 8-byte split of `u64.bv`.
  let bv : BitVec 64 := u64.bv
  let off : Nat := 8 * (b % 8)
  ⟨BitVec.ofNat 8 ((bv.toNat >>> off) &&& 0xff)⟩

/-- The outer fixpoint of `state.store_block_2u32_loop` terminates with
    `.ok` and preserves the length of the output slice, provided the
    preconditions hold. -/
@[spec]
theorem state.store_block_2u32_loop_spec
    (iter : core_models.ops.range.Range Std.Usize)
    (s : state.KeccakState) (out : Slice Std.U8)
    (h_le : iter.start.val ≤ iter.end.val)
    (h_bnd : iter.end.val ≤ 25)
    (h_off : 8 * iter.end.val ≤ Std.Usize.max)
    (h_blk : 8 * iter.end.val ≤ out.val.length) :
    ⦃ ⌜ True ⌝ ⦄
    state.store_block_2u32_loop iter s out
    ⦃ ⇓ r => ⌜ r.val.length = out.val.length ⌝ ⦄ := by
  obtain ⟨iter_start, iter_end⟩ := iter
  unfold state.store_block_2u32_loop
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, out1) => state.store_block_2u32_loop.body s iter1 out1)
      out iter_start iter_end
      (fun _ out1 => pure (out1.val.length = out.val.length))
      h_le
      (pure_prop_holds rfl)
      ?_)
  · rw [PostCond.entails_noThrow]
    intro r h
    exact of_pure_prop_holds h
  · intro acc k h_ge h_le_k hinv
    have h_acc_len : acc.val.length = out.val.length := of_pure_prop_holds hinv
    unfold state.store_block_2u32_loop.body
    apply Std.Do.Triple.bind _ _
      (IteratorRange_next_spec_usize k iter_end
        (Q := PostCond.noThrow fun (oi : Option Std.Usize × _) => ⌜
          match oi.1 with
          | none => k.val ≥ iter_end.val ∧
                    oi.2 = { start := k, «end» := iter_end }
          | some i => i = k ∧ k.val < iter_end.val ∧
                      oi.2.«end» = iter_end ∧ oi.2.start.val = k.val + 1
        ⌝)
        (fun hlt s' hs' => by
          dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
          exact ⟨rfl, hlt, rfl, hs'⟩)
        (fun hge => by
          dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
          exact ⟨hge, rfl⟩))
    intro ⟨o, iter1⟩
    apply triple_imp_intro
    rcases o with _ | i
    · rintro ⟨hge, hiter1_eq⟩
      show ⦃⌜True⌝⦄ (Aeneas.Std.Result.ok (done acc) : Result _) ⦃_⦄
      exact triple_of_ok_local rfl (pure_prop_holds h_acc_len)
    · rintro ⟨hi_eq, hk_lt, hiter1_end, hiter1_start⟩
      cases hi_eq
      have hk_25 : k.val < 25 := by
        have h1 : k.val < iter_end.val := hk_lt
        have h2 : iter_end.val ≤ 25 := h_bnd
        omega
      have hk_div : k.val / 5 < 5 := by omega
      have hk_mod : k.val % 5 < 5 := Nat.mod_lt _ (by decide)
      -- Bounds for the two 4-byte writes (offsets 8*k and 8*k+4).
      have h_b1 : 8 * k.val + 4 ≤ acc.val.length := by
        have h1 : 8 * k.val + 8 ≤ 8 * iter_end.val := by omega
        have h2 : 8 * iter_end.val ≤ out.val.length := h_blk
        omega
      have h_b2 : 8 * k.val + 8 ≤ acc.val.length := by
        have h1 : 8 * k.val + 8 ≤ 8 * iter_end.val := by omega
        have h2 : 8 * iter_end.val ≤ out.val.length := h_blk
        omega
      have h_smax1 : 8 * k.val + 4 ≤ Std.Usize.max := by
        have h1 : 8 * k.val + 8 ≤ 8 * iter_end.val := by omega
        have h2 : 8 * iter_end.val ≤ Std.Usize.max := h_off
        omega
      have h_smax2 : 8 * k.val + 8 ≤ Std.Usize.max := by
        have h1 : 8 * k.val + 8 ≤ 8 * iter_end.val := by omega
        have h2 : 8 * iter_end.val ≤ Std.Usize.max := h_off
        omega
      unfold state.KeccakState.get_lane
             lane.Lane2U32.Insts.Core_modelsOpsIndexIndexUsizeU32.index
      mvcgen
      -- Remaining VCs after `mvcgen`:
      --   `vc14.h1`: `↑r_13 ≤ ((r_8.2 r_11).val).length` — rewrite via
      --              `h_8.2.2`, then `List.length_setSlice!` reduces to
      --              the `acc`-length bound `h_b2`.
      --   `vc16.h`:  `(r_14.1.val).length = (r_16.to_slice).length`
      --              — `h_14.2.1` gives LHS = 4, `Array.length_to_slice`
      --              gives RHS = 4.
      --   `vc17`:    `pure ((r_14.2 r_17).val.length = out.val.length)`
      --              `r_14.2 r_17 = (r_8.2 r_11).setSlice! r_12 r_17` and
      --              `r_8.2 r_11 = acc.setSlice! r_6 r_11`. Two
      --              `List.length_setSlice!` rewrites close it.
      -- All other VCs are scalar bounds, dispatched by `scalar_tac`.
      case vc14.h1 =>
        expose_names
        rw [h_8.2.2 r_11, List.length_setSlice!]
        scalar_tac
      case vc16.h =>
        expose_names
        -- Goal: `(↑r_14.1).length = (↑r_16.to_slice).length`. The LHS reduces to
        -- `r_13 - r_12 = 4` via `h_14.2.1`; the RHS reduces to `4` since
        -- `r_16 : Array U8 4#usize` and `to_slice` preserves `.val`.
        rw [h_14.2.1]
        simp only [Aeneas.Std.Array.to_slice, Aeneas.Std.Array.length_eq]
        scalar_tac
      case vc17 =>
        expose_names
        refine ⟨hk_lt, hiter1_end, hiter1_start, ?_⟩
        apply pure_prop_holds
        rw [h_14.2.2 r_17, List.length_setSlice!, h_8.2.2 r_11,
            List.length_setSlice!]
        exact h_acc_len
      all_goals scalar_tac

end libcrux_iot_sha3.Sponge
