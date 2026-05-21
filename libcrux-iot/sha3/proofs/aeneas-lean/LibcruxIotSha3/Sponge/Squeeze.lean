/-
  # Phase 5 — squeeze loop (`keccak_loop1`) and per-byte spec bridge.

  Artifacts delivered in this file:

  * `iterate_keccak_f_eq_fold` — pure unfold of `sponge.iterate_keccak_f`
    to a `Nat.fold` of `keccak_f.keccak_f`. Proved by induction on the
    iteration count using `sponge.iterate_keccak_f.eq_def`.

  * `keccak.keccak_loop1_invariant` — the impl Triple for the squeeze
    loop `keccak.keccak_loop1`. Uses `loop_range_spec_usize` with a
    fold-form invariant carrying termination (`r.i.val = 0`), offset
    advancement, and spec-side lockstep
    `squeeze_fold s (blocks - 1) = .ok (lift r)`.

  * `squeeze_byte_at` — the per-byte projection of a spec state used
    by both `keccak.squeeze_next_block_spec` and the eventual
    per-byte equivalence theorem.

  ## Deferred (TODO)

  * `sponge_squeeze_byte_eq` — the pure block-wise characterization
    of `sponge.squeeze`. Equates byte `k` of `sponge.squeeze` (under
    `iterate_keccak_f (k/rate) state = .ok s_b`) with
    `squeeze_byte_at s_b (k % rate.val)`. Proof path: use
    `createi_pure_spec` on the squeeze closure, then unfold the
    closure body's arithmetic (`/`, `*`, `-`, `byte_lane_idx`,
    `Array.index_usize`, `U64.to_le_bytes`). All steps reduce to
    closed forms under `rate.val > 0` and `rate.val % 8 = 0`, but
    the per-step VC bookkeeping is substantial. Establishing
    `iterate_keccak_f` totality (needed to chain success across
    all `OUTPUT_LEN` byte indices) requires a `keccak_f.keccak_f`
    totality lemma, currently available only as a Triple on lifted
    impl states via Bridge 1's `keccakf1600_equiv_hacspec`.

  ## See also

  - `Sponge/Plan.lean` § 5 — full Plan post target.
  - `Sponge/SqueezeBlock.lean:keccak.squeeze_next_block_spec` —
    per-block Triple used in the loop body.
-/
import LibcruxIotSha3.Sponge.SqueezeBlock

open Aeneas Aeneas.Std Result Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Sponge

open libcrux_iot_sha3.Equivalence

-- Defensive seal re-issue: no proof in this file may unfold either side
-- of Bridge 1.
set_option allowUnsafeReducibility true in
attribute [local irreducible] keccak.keccakf1600 keccak_f.keccak_f

/-! ## Phase 5 — squeeze loop. -/

/-! ### Local helpers (mirror of `Absorb.lean`). -/

private theorem triple_of_ok_sq {α : Type} {x : Result α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, hp]

private theorem triple_exists_ok_sq {α : Type} {x : Result α}
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

/-! ### Theorem 1: `iterate_keccak_f_eq_fold`.

The spec's `sponge.iterate_keccak_f n state` equals the `Nat.fold` of
`keccak_f.keccak_f` over `n.val`. Proved by Nat-induction. -/

/-- Pure `Nat.fold` form of `sponge.iterate_keccak_f`. At index `n`, this
    is the right-associated chain of `keccak_f.keccak_f` calls. -/
def iterate_keccak_f_fold (state : Std.Array Std.U64 25#usize) (n : Nat) :
    Result (Std.Array Std.U64 25#usize) :=
  Nat.fold n (init := (.ok state : Result _))
    (fun _ _ acc => acc >>= fun st => keccak_f.keccak_f st)

theorem iterate_keccak_f_eq_fold
    (n : Std.Usize) (state : Std.Array Std.U64 25#usize) :
    sponge.iterate_keccak_f n state = iterate_keccak_f_fold state n.val := by
  -- Induction on `m := n.val`, generalized over state and n.
  suffices h : ∀ (m : Nat) (n : Std.Usize) (state : Std.Array Std.U64 25#usize),
      n.val = m → sponge.iterate_keccak_f n state = iterate_keccak_f_fold state m
    by exact h n.val n state rfl
  intro m
  induction m with
  | zero =>
    intro n state h_n_val
    rw [sponge.iterate_keccak_f.eq_def]
    have h_n_eq : n = 0#usize := by
      apply Std.UScalar.eq_of_val_eq
      rw [h_n_val]; rfl
    rw [h_n_eq]; simp only [↓reduceIte]
    unfold iterate_keccak_f_fold
    simp only [Nat.fold_zero]
  | succ k ih =>
    intro n state h_n_val
    rw [sponge.iterate_keccak_f.eq_def]
    have h_n_nz : ¬ n = 0#usize := by
      intro h
      have : n.val = 0 := by rw [h]; rfl
      omega
    simp only [h_n_nz, ↓reduceIte]
    -- Now reduce `n - 1#usize`. Use `sub_equiv`-style direct reduction.
    set i : Std.Usize := ⟨BitVec.ofNat _ (n.val - 1)⟩ with hi_def
    have h_n_ge : ¬ n.val < (1#usize : Std.Usize).val := by
      show ¬ n.val < 1; rw [h_n_val]; omega
    have h_sub_eq : n - 1#usize = (.ok i : Result Std.Usize) := by
      show Std.UScalar.sub n 1#usize = .ok i
      unfold Std.UScalar.sub
      rw [if_neg h_n_ge]
      rfl
    have h_i_val : i.val = k := by
      show (BitVec.ofNat _ (n.val - 1)).toNat = k
      rw [BitVec.toNat_ofNat]
      have h_bound : n.val - 1 < 2 ^ Std.UScalarTy.Usize.numBits := by
        have := n.hBounds
        simp [Std.UScalarTy.numBits] at *
        omega
      rw [Nat.mod_eq_of_lt h_bound, h_n_val]; omega
    rw [h_sub_eq]; simp only [bind_tc_ok]
    -- IH on i.
    rw [ih i state h_i_val]
    -- Goal: `iterate_keccak_f_fold state k >>= keccak_f.keccak_f
    --      = iterate_keccak_f_fold state (k+1)`.
    unfold iterate_keccak_f_fold
    rw [Nat.fold_succ]

/-! ### Theorem 2: `sponge_squeeze_byte_eq`.

Per-byte characterization of `sponge.squeeze`. For each byte index
`k < OUTPUT_LEN.val`, byte `k` of `sponge.squeeze OUTPUT_LEN state rate`
equals the byte-projection of `iterate_keccak_f (k/rate) state` at
position `k % rate`. -/

/-- Per-byte projection of a spec state: byte `j` of the lane-major
    serialization of `s`. Matches the per-byte formula used in
    `keccak.squeeze_next_block_spec` and is the form that
    `sponge.squeeze` produces for byte `k = b*rate + j` of the OUTPUT
    (with `b = k/rate`, `j = k % rate < rate`).

    Used in Theorem 3's loop invariant to bridge impl-side per-byte
    output to the spec's `iterate_keccak_f`-driven squeeze. The
    bridge (Theorem 2: `sponge_squeeze_byte_eq`) — the per-byte
    equality `(sponge.squeeze ...).val[k]! = squeeze_byte_at (iterate
    state) (k % rate)` — is deferred: it is a pure unfolding of the
    `createi`-closure (using `createi_pure_spec`), and the per-cell
    computation involves several `Usize` arithmetic operations that
    must each be reduced to closed form. The key invariant that
    iterate_keccak_f always succeeds requires a totality lemma for
    `keccak_f.keccak_f`, currently established only on lifted impl
    states via Bridge 1's `keccakf1600_equiv_hacspec`. See Plan §5
    risks. -/
def squeeze_byte_at (s : Std.Array Std.U64 25#usize) (j : Nat) : Std.U8 :=
  ⟨(BitVec.toLEBytes (s.val[5 * ((j / 8) % 5) + (j / 8) / 5]!).bv)[j % 8]!⟩

/-! The squeeze closure stored state is `(rate, state)`. When invoked at
    index `k`, it computes `b = k/rate`, `j = k - b*rate`, runs
    `iterate_keccak_f b state` to get `s_b`, then extracts byte
    `byte_lane_idx (j/8) = 5*((j/8)%5) + (j/8)/5` of `s_b` and projects
    byte `j%8` of the little-endian representation.

    To package the closure-call result as a clean equation we need: -/

/-- For `k ≤ Usize.max`, `(BitVec.ofNat _ k).toNat = k`. -/
private theorem usize_ofNat_toNat (k : Nat) (h : k ≤ Std.Usize.max) :
    (BitVec.ofNat Std.UScalarTy.Usize.numBits k).toNat = k := by
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have h1 : Std.UScalarTy.Usize.numBits = Std.Usize.numBits := by
    rw [Std.Usize.numBits]
  rw [h1]
  have hpos : 0 < 2 ^ Std.Usize.numBits := Nat.two_pow_pos _
  have h2 : 2 ^ Std.Usize.numBits = Std.Usize.max + 1 := by
    rw [Std.Usize.max]; omega
  omega

/-- The Aeneas `Usize` value built from `BitVec.ofNat _ k`, for `k ≤ Usize.max`. -/
private def usize_of_nat (k : Nat) (_h : k ≤ Std.Usize.max) : Std.Usize :=
  ⟨BitVec.ofNat _ k⟩

@[simp] private theorem usize_of_nat_val (k : Nat) (h : k ≤ Std.Usize.max) :
    (usize_of_nat k h).val = k :=
  usize_ofNat_toNat k h

/-! ### Helper Triple: `RangeFromUsize` mutable slice index.

Companion to `Absorb.lean:core_models_Slice_Insts_index_RangeFromUsize_spec`
(non-mut version) and `SliceSpecs.lean:core_models_Slice_Insts_index_mut_RangeUsize_spec`
(closed range). The mutable `RangeFrom` variant is what `keccak_loop1.body`
uses to obtain the tail sub-slice. -/
@[spec]
theorem core_models_Slice_Insts_index_mut_RangeFromUsize_spec
    {T : Type} (s : Slice T) (r : core_models.ops.range.RangeFrom Std.Usize)
    (h : r.start.val ≤ s.val.length) :
    ⦃ ⌜ True ⌝ ⦄
    core_models.Slice.Insts.Core_modelsOpsIndexIndexMut.index_mut
      (core_models.ops.range.RangeFromUsize.Insts.Core_modelsSliceIndexSliceIndexSliceSlice T) s r
    ⦃ ⇓ p => ⌜ p.1.val = s.val.drop r.start.val ∧
                p.1.val.length = s.val.length - r.start.val ∧
                ∀ s', (p.2 s').val = s.val.setSlice! r.start.val s'.val ⌝ ⦄ := by
  unfold core_models.Slice.Insts.Core_modelsOpsIndexIndexMut.index_mut
         core_models.ops.range.RangeFromUsize.Insts.Core_modelsSliceIndexSliceIndexSliceSlice
         core_models.cmRangeFromUsizeToAeneas
         core.slice.index.Slice.index_mut
         core.slice.index.SliceIndexRangeUsizeSlice.index_mut
  have h0' : (⟨r.start, s.len⟩ : core.ops.range.Range Std.Usize).start
              ≤ (⟨r.start, s.len⟩ : core.ops.range.Range Std.Usize).end := by
    simpa [UScalar.le_equiv, Std.Slice.len, Std.Slice.length] using h
  simp only [Triple, WP.wp]
  simp [h0', Std.Slice.length, Std.Slice.len]
  refine ⟨?_, ?_⟩
  · unfold List.slice
    rw [List.take_of_length_le]
    rw [List.length_drop]
  · unfold List.slice
    rw [List.length_take, List.length_drop]
    omega

/-! ### Theorem 3: `keccak.keccak_loop1_invariant`.

The impl-side squeeze loop equals a `Nat.fold` of `keccak_f.keccak_f` on
the spec state.

The loop iterates from `1..blocks`, applying ONE `keccakf1600` per
iteration. After all iterations, the state has had `blocks - 1`
applications, and the offset has advanced by `(blocks - 1) * RATE`. -/

/-- The fold-form invariant accumulator on the spec side. After `k`
    iterations of the loop body, the impl state corresponds to
    `iterate_keccak_f_fold (lift s_init) k`. -/
def squeeze_fold (s_init : state.KeccakState) (k : Nat) :
    Result (Std.Array Std.U64 25#usize) :=
  iterate_keccak_f_fold (Equivalence.lift s_init) k

@[spec]
theorem keccak.keccak_loop1_invariant
    (RATE : Std.Usize) (blocks : Std.Usize) (s : state.KeccakState)
    (out : Slice Std.U8) (offset : Std.Usize)
    (h_i : s.i.val = 0)
    (h_RATE_mod : RATE.val % 8 = 0)
    (h_RATE_bnd : RATE.val ≤ 200)
    (h_blocks_pos : 1 ≤ blocks.val)
    (h_offset : offset.val + (blocks.val - 1) * RATE.val ≤ out.val.length)
    (h_offset_max : offset.val + (blocks.val - 1) * RATE.val ≤ Std.Usize.max) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccak_loop1 RATE { start := 1#usize, «end» := blocks } out s offset
    ⦃ ⇓ r => ⌜
        let (out_final, s_final, offset_final) := r
        out_final.val.length = out.val.length
        ∧ s_final.i.val = 0
        ∧ offset_final.val = offset.val + (blocks.val - 1) * RATE.val
        ∧ squeeze_fold s (blocks.val - 1) = .ok (Equivalence.lift s_final)
    ⌝ ⦄ := by
  unfold keccak.keccak_loop1
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, out1, s1, offset1) =>
        keccak.keccak_loop1.body RATE iter1 out1 s1 offset1)
      (out, s, offset) 1#usize blocks
      (fun k acc => pure (
          acc.1.val.length = out.val.length
          ∧ acc.2.1.i.val = 0
          ∧ acc.2.2.val = offset.val + (k.val - 1) * RATE.val
          ∧ squeeze_fold s (k.val - 1) = .ok (Equivalence.lift acc.2.1)))
      h_blocks_pos
      (pure_prop_holds ⟨rfl, h_i, by
          show offset.val = offset.val + ((1#usize : Std.Usize).val - 1) * RATE.val
          show offset.val = offset.val + (1 - 1) * RATE.val
          simp,
        by
          show squeeze_fold s ((1#usize : Std.Usize).val - 1) = _
          show squeeze_fold s (1 - 1) = _
          show squeeze_fold s 0 = _
          unfold squeeze_fold iterate_keccak_f_fold
          rfl⟩)
      ?_)
  · rw [PostCond.entails_noThrow]
    intro r h
    obtain ⟨h1, h2, h3, h4⟩ := of_pure_prop_holds h
    refine ⟨h1, h2, ?_, ?_⟩
    · rw [h3]
    · exact h4
  · intro acc k h_ge h_le_k hinv
    obtain ⟨h_acc_len, h_acc_i, h_acc_offset, h_fold_acc⟩ := of_pure_prop_holds hinv
    obtain ⟨out_acc, s_acc, offset_acc⟩ := acc
    -- Body: keccak.keccak_loop1.body RATE { start := k, end := blocks } out_acc s_acc offset_acc.
    unfold keccak.keccak_loop1.body
    apply Std.Do.Triple.bind _ _
      (IteratorRange_next_spec_usize k blocks
        (Q := PostCond.noThrow fun (oi : Option Std.Usize × _) => ⌜
          match oi.1 with
          | none => k.val ≥ blocks.val ∧
                    oi.2 = { start := k, «end» := blocks }
          | some i => i = k ∧ k.val < blocks.val ∧
                      oi.2.«end» = blocks ∧ oi.2.start.val = k.val + 1
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
    · rintro ⟨hge, _⟩
      have hk_eq : k.val = blocks.val := Nat.le_antisymm h_le_k hge
      simp only [Triple, WP.wp]
      apply SPred.pure_intro
      refine pure_prop_holds ⟨h_acc_len, h_acc_i, ?_, ?_⟩
      · rw [h_acc_offset, hk_eq]
      · rw [← hk_eq]; exact h_fold_acc
    · rintro ⟨hi_eq, hk_lt, hiter1_end, hiter1_start⟩
      cases hi_eq
      -- Side-condition: `offset_acc + RATE ≤ out_acc.length`.
      have h_off_lt_outlen : offset_acc.val + RATE.val ≤ out_acc.val.length := by
        rw [h_acc_len, h_acc_offset]
        have hk_ge_1 : 1 ≤ k.val := h_ge
        have h_k_blocks_minus_1 : k.val ≤ blocks.val - 1 := by omega
        have h_arith : (k.val - 1) * RATE.val + RATE.val = k.val * RATE.val := by
          have : k.val = (k.val - 1) + 1 := by omega
          conv_rhs => rw [this]
          rw [Nat.add_mul]; ring
        have : offset.val + (k.val - 1) * RATE.val + RATE.val
              = offset.val + k.val * RATE.val := by
          rw [Nat.add_assoc, h_arith]
        rw [this]
        have h_step : k.val * RATE.val ≤ (blocks.val - 1) * RATE.val :=
          Nat.mul_le_mul_right RATE.val h_k_blocks_minus_1
        omega
      have h_off_RATE_max : offset_acc.val + RATE.val ≤ Std.Usize.max := by
        rw [h_acc_offset]
        have hk_ge_1 : 1 ≤ k.val := h_ge
        have h_k_blocks_minus_1 : k.val ≤ blocks.val - 1 := by omega
        have h_arith : (k.val - 1) * RATE.val + RATE.val = k.val * RATE.val := by
          have : k.val = (k.val - 1) + 1 := by omega
          conv_rhs => rw [this]
          rw [Nat.add_mul]; ring
        have : offset.val + (k.val - 1) * RATE.val + RATE.val
              = offset.val + k.val * RATE.val := by
          rw [Nat.add_assoc, h_arith]
        rw [this]
        have h_step : k.val * RATE.val ≤ (blocks.val - 1) * RATE.val :=
          Nat.mul_le_mul_right RATE.val h_k_blocks_minus_1
        omega
      -- The body unfolds to a chain. Use mvcgen to discharge the body
      -- using the specs we have.
      mvcgen
      all_goals (try scalar_tac)
      -- One remaining VC: invariant preservation.
      expose_names
      obtain ⟨h_idx_drop, h_idx_len, h_back⟩ := h
      obtain ⟨h_snb_i, h_snb_len, s_spec, h_snb_spec, h_snb_lift, h_snb_bytes⟩ := h_1
      refine ⟨hk_lt, hiter1_end, hiter1_start, ?_⟩
      apply pure_prop_holds
      refine ⟨?_, h_snb_i, ?_, ?_⟩
      · -- Length: `(back snb_out).val.length = out.val.length`.
        rw [h_back]
        rw [List.length_setSlice!]
        exact h_acc_len
      · -- offset_new.val = offset.val + (iter1.start.val - 1) * RATE.val.
        rw [h_2, h_acc_offset, hiter1_start]
        have hk_ge_1 : 1 ≤ k.val := h_ge
        have h_arith : (k.val - 1) * RATE.val + RATE.val
                      = (k.val + 1 - 1) * RATE.val := by
          have h1 : k.val + 1 - 1 = k.val := by omega
          rw [h1]
          have h2 : k.val = (k.val - 1) + 1 := by omega
          conv_rhs => rw [h2]
          rw [Nat.add_mul]; ring
        omega
      · -- squeeze_fold s (iter1.start.val - 1) = .ok (lift r_snb.1).
        rw [hiter1_start]
        show squeeze_fold s (k.val + 1 - 1) = _
        have hk_ge_1 : 1 ≤ k.val := h_ge
        have h_idx : k.val + 1 - 1 = (k.val - 1) + 1 := by omega
        rw [h_idx]
        unfold squeeze_fold iterate_keccak_f_fold
        rw [Nat.fold_succ]
        have h_inner :
            (Nat.fold (k.val - 1) (init := (.ok (Equivalence.lift s) : Result _))
              (fun _ _ acc => acc >>= fun st => keccak_f.keccak_f st))
            = .ok (Equivalence.lift s_acc) := by
          have := h_fold_acc
          unfold squeeze_fold iterate_keccak_f_fold at this
          exact this
        rw [h_inner]; simp only [bind_tc_ok]
        rw [h_snb_spec]
        rw [h_snb_lift]

end libcrux_iot_sha3.Sponge
