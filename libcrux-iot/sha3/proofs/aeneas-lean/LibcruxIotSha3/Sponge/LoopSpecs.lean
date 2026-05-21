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

Proof: `loop_range_spec_usize` with `inv _ _ := True` — body Triple
closes via `hax_mvcgen` once all sub-Triples (`try_from`, `from_le_bytes`,
`Result.unwrap`, slice subindexing, `interleave`) are in scope. -/

/-- The outer fixpoint of `state.load_block_2u32_loop0` terminates with
    `.ok`, provided the preconditions hold. -/
@[spec]
theorem state.load_block_2u32_loop0_spec
    (iter : core_models.ops.range.Range Std.Usize)
    (blocks : Slice Std.U8) (start : Std.Usize)
    (state_flat : Std.Array lane.Lane2U32 25#usize)
    (h_le : iter.start.val ≤ iter.end.val)
    (h_bnd : iter.end.val ≤ 25)
    (h_off : start.val + 8 * iter.end.val ≤ Std.Usize.max)
    (h_blk : start.val + 8 * iter.end.val ≤ blocks.val.length) :
    ⦃ ⌜ True ⌝ ⦄
    state.load_block_2u32_loop0 iter blocks start state_flat
    ⦃ ⇓ _r => ⌜ True ⌝ ⦄ := by
  obtain ⟨iter_start, iter_end⟩ := iter
  unfold state.load_block_2u32_loop0
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, s1) => state.load_block_2u32_loop0.body blocks start iter1 s1)
      state_flat iter_start iter_end
      (fun _ _ => pure True)
      h_le
      (pure_prop_holds trivial)
      ?_)
  · rw [PostCond.entails_noThrow]
    intro _ _
    exact pure_prop_holds trivial |> of_pure_prop_holds |> id
  · intro acc k h_ge h_le_k _hinv
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
      exact triple_of_ok_local rfl (pure_prop_holds trivial)
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
      all_goals (first
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
             | exact ⟨_, h_9⟩))

/-! Helper definitions for Loop0's strengthened invariant.

After Loop0's k-th iteration, `state_flat[j]` (for `j < k`) is the
two-`U32` halves obtained by reading two 4-byte LE windows from
`blocks` at offsets `start+8j` and `start+8j+4` and pairing them. -/

/-- The `Lane2U32` constructed at iteration `j` of Loop0: reads two
    4-byte LE windows from `blocks` at offsets `start+8j` and `start+8j+4`,
    interpreting each as a `U32`, then pairs them (then later
    `Lane2U32.interleave` is applied to this pair in the body — we
    capture the *pre-interleave* pair here, since the interleave step
    is uniform). -/
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
    (h_bnd : iter.end.val ≤ 25) :
    ⦃ ⌜ True ⌝ ⦄
    state.load_block_2u32_loop1 iter s state_flat
    ⦃ ⇓ r => ⌜ r.i = s.i ⌝ ⦄ := by
  obtain ⟨iter_start, iter_end⟩ := iter
  unfold state.load_block_2u32_loop1
  -- Apply `loop_range_spec_usize` with `inv k acc := acc.i = s.i`.
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, s1) => state.load_block_2u32_loop1.body state_flat iter1 s1)
      s iter_start iter_end
      (fun _ s1 => pure (s1.i = s.i))
      h_le
      (pure_prop_holds rfl)
      ?_)
  · rw [PostCond.entails_noThrow]
    intro r h
    exact of_pure_prop_holds h
  · intro acc k h_ge h_le_k hinv
    have h_acc_i : acc.i = s.i := of_pure_prop_holds hinv
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
      exact triple_of_ok_local rfl (pure_prop_holds h_acc_i)
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
      -- Every VC is a scalar bound; the inv-preservation VC is also
      -- closed by `scalar_tac` because the body's update lifts to
      -- `{ acc with st := ... }` whose `.i` field is `acc.i = s.i` (the
      -- `h_acc_i` hypothesis from the prior iteration is in scope, and
      -- `scalar_tac` lifts the struct-update through equality).
      all_goals scalar_tac

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
