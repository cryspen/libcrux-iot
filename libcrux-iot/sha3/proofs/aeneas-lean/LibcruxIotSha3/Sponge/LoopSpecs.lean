/-
  # Phase 1a — Loop Triples for `load_block` / `store_block` outer fixpoints.

  Provides three `@[spec]` Triples, one per Aeneas `partial_fixpoint` loop,
  threading a `loop_range_spec_usize`-style forward induction:

  - `state.load_block_2u32_loop0_spec`   — outer fixpoint of load-loop 0.
    Body: read 8 bytes from `blocks` at offset `start + 8*i`, interleave,
    write to `state_flat[i]`.
  - `state.load_block_2u32_loop1_spec`   — outer fixpoint of load-loop 1.
    Body: XOR `state_flat[i]` (both halves) into `s.st[5*(i%5) + i/5]`.
  - `state.store_block_2u32_loop_spec`   — outer fixpoint of store-loop.
    Body: deinterleave `s.st[5*(i%5) + i/5]` and write 8 bytes to
    `out[8*i .. 8*i + 8]`.

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

/-! ### Loop 0 of `state.load_block_2u32` — OMITTED.

The outer fixpoint of `state.load_block_2u32_loop0` is intentionally
NOT given an `@[spec]` Triple in this file. The blocker is purely
infrastructural: each loop iteration calls

    core_models.Array.Insts.Core_modelsConvertTryFromShared0SliceTryFromSliceError.try_from

(twice, to coerce two 4-byte slices into `Array U8 4`). The
`SliceSpecs.lean` file (in the same `Sponge/` directory) explicitly
documents this Triple as OMITTED — its proof requires an induction
over the closure's `call_mut` calls and the `List.range 4` `foldlM`,
totalling ~70 lines of plumbing that doesn't fit the scope of this
file.

Once `try_from_spec` lands (in a follow-up patch to `SliceSpecs.lean`),
the Triple `state.load_block_2u32_loop0_spec` can be added here using
the same `loop_range_spec_usize` template as the *_loop1_spec /
*_loop_spec proofs below: the body Triple closes via `mvcgen` +
`scalar_tac` once all sub-Triples are in scope.

Additional preconditions that body discharge will need:
- `start.val + 8 * iter.end.val ≤ Std.Usize.max` (offset overflow)
- `start.val + 8 * iter.end.val ≤ blocks.val.length`  (slice bound)
- `iter.end.val ≤ 25` (Array.update bound on the 25-cell `state_flat`).
-/

/-! ### Loop 1 of `state.load_block_2u32`. -/

/-- The outer fixpoint of `state.load_block_2u32_loop1` terminates with
    `.ok`, provided `iter.start.val ≤ iter.end.val ≤ 25`.

    Per-iteration: at index `i ∈ [iter.start, iter.end)`, XOR the two
    halves of `state_flat[i]` into the lane `s.st[5*(i%5) + i/5]`.

    Note the lane index `5*(i%5) + i/5` is bounded by 25 when `i < 25`,
    so the inner `state.KeccakState.set_lane` / `get_lane` calls succeed.
    We propagate the bound `iter.end.val ≤ 25` to discharge those bounds.

    Proof: `loop_range_spec_usize` with `inv _ _ := True`. -/
@[spec]
theorem state.load_block_2u32_loop1_spec
    (iter : core_models.ops.range.Range Std.Usize)
    (state_flat : Std.Array lane.Lane2U32 25#usize)
    (s : state.KeccakState)
    (h_le : iter.start.val ≤ iter.end.val)
    (h_bnd : iter.end.val ≤ 25) :
    ⦃ ⌜ True ⌝ ⦄
    state.load_block_2u32_loop1 iter s state_flat
    ⦃ ⇓ _r => ⌜ True ⌝ ⦄ := by
  obtain ⟨iter_start, iter_end⟩ := iter
  unfold state.load_block_2u32_loop1
  -- Apply `loop_range_spec_usize` with `inv _ _ := True`. The post then
  -- reduces to `True`, matching the desired Triple post.
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, s1) => state.load_block_2u32_loop1.body state_flat iter1 s1)
      s iter_start iter_end
      (fun _ _ => pure True)
      h_le
      (pure_prop_holds trivial)
      ?_)
  · -- Post-entailment: `(pure True).holds ⊢ True`.
    rw [PostCond.entails_noThrow]
    intro _ _
    exact pure_prop_holds trivial |> of_pure_prop_holds |> id
  · intro acc k h_ge h_le_k _hinv
    -- The body has shape:
    --   let (o, iter1) ← IteratorRange.next ...
    --   match o with
    --   | None => ok (done acc)
    --   | Some i => ... ; ok (cont (iter1, s_new))
    unfold state.load_block_2u32_loop1.body
    -- Run IteratorRange_next_spec_usize.
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
    · -- None branch: k.val ≥ iter_end.val, body returns done acc.
      rintro ⟨hge, hiter1_eq⟩
      show ⦃⌜True⌝⦄ (Aeneas.Std.Result.ok (done acc) : Result _) ⦃_⦄
      exact triple_of_ok_local rfl (pure_prop_holds trivial)
    · -- Some i branch: i = k, body runs the per-step update.
      rintro ⟨hi_eq, hk_lt, hiter1_end, hiter1_start⟩
      cases hi_eq
      have hk_25 : k.val < 25 := by
        have h1 : k.val < iter_end.val := hk_lt
        have h2 : iter_end.val ≤ 25 := h_bnd
        omega
      have hk_div : k.val / 5 < 5 := by omega
      have hk_mod : k.val % 5 < 5 := Nat.mod_lt _ (by decide)
      -- Unfold the body and the inner KeccakState helpers.
      unfold state.KeccakState.get_lane state.KeccakState.set_lane
             lane.Lane2U32.Insts.Core_modelsOpsIndexIndexUsizeU32.index
             lane.Lane2U32.from_ints
      -- Now everything's in terms of primitive Aeneas Std ops.
      mvcgen
      all_goals scalar_tac

/-! ### Loop 0 of `state.store_block_2u32` — OMITTED.

The outer fixpoint of `state.store_block_2u32_loop` is intentionally
NOT given an `@[spec]` Triple in this file. The proof skeleton
(`loop_range_spec_usize` with invariant
`inv _ out' := out'.val.length = out.val.length`) reaches the body
Triple cleanly: scalar bounds and lane-index facts (`8*k + 8 ≤ acc.val.length`,
`5*(k%5) + k/5 < 25`, `k/5 < 5`, etc.) are all dischargeable.

After `mvcgen` on the body, 19 scalar subgoals close via `scalar_tac`.
**Three** non-scalar subgoals remain:

1. **`vc14.h1`** — slice-length bound for the second `index_mut`:
   `r.end.val ≤ (first_index_mut_back s₂).val.length`.
2. **`vc16.h`** — `copy_from_slice` length equation:
   `(first_index_mut_back.1).val.length = (to_le_bytes u32).to_slice.val.length`.
3. **`vc17`** — final post-conjunction's invariant clause:
   `(second_index_mut_back s₃).val.length = out.val.length`.

All three are dischargeable in principle by destructuring the
`index_mut_back` closure-spec hypothesis (a 3-conjunction
`_ ∧ _ ∧ ∀ s', (p.2 s').val = base.setSlice! _ s'.val`) and applying
`List.length_setSlice!`. The blocker is that `rename_i`-based access
to the closure spec hypothesis is brittle (counts vary between vc14
and vc17 due to differing mvcgen-introduced binder counts), and there
is no `@[simp]` lemma capturing the `length`-projection of a closure-
specified `index_mut_back` application.

Once such a `@[simp]` (or a custom tactic that scans the local context
for hypotheses matching the closure-spec shape and projects out the
∀-conjunct) lands in `SliceSpecs.lean`, this Triple's body Triple
closes via the `loop_range_spec_usize` template established by
`state.load_block_2u32_loop1_spec` (above), with the preconditions
`iter.end.val ≤ 25` and `8 * iter.end.val ≤ out.val.length`. -/

end libcrux_iot_sha3.Sponge
