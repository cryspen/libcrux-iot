/-
  Campaign 2 (algebraic): the pure-Lean bit_keccak_spec equals the hacspec
  24-round application under the canonical lift.

  Outline:

  1. Per-round step functions `bit_round0..3 : KState → KState` (composing
     `theta + pi_rho_chi_1 + pi_rho_chi_2` per round).
  2. `bit_keccakf1600_4rounds_eq_chain` (`bit_keccakf1600_4rounds 0 s =
     bit_round3 (bit_round2 (bit_round1 (bit_round0 s)))`) — by `rfl`,
     since both sides unfold to the same 12-call let-chain.
  3. KState round-trip `KState.toAeneas (KState.fromAeneas s) = s` — bridges
     Campaign 1's pure-Lean output back into the Aeneas universe for the
     spec equation. Needed at the top-level composition.
  4. Per-round algebraic correspondence theorems
     `bit_round{k}_alg_eq` (k ∈ {0,1,2,3}) — the load-bearing algebra
     of Campaign 2. Each says
     `spec_round_step (lift_perm s.toAeneas (impl_perm^[k]) impl_swap) s.i`
     `  = .ok (lift_perm (bit_round{k} s).toAeneas (impl_perm^[k+1]) impl_swap)`.
     *Currently `sorry` — see per-theorem docstrings for proof plans.*
  5. 4-round closure `bit_4rounds_alg_eq` — composes the 4 sorry'd
     per-round identities through `Result.bind`. Uses `impl_perm_pow4_eq_id`
     to collapse `impl_perm^[4]` to `id` at the group boundary.
  6. 24-round closure `bit_keccak_alg_eq` — 6-iteration induction over
     `Nat.iterate (bit_keccakf1600_4rounds 0) 6`. Threads the `s.i.val =
     4k` chain to align iota constants.
  7. Top-level `keccakf1600_equiv_via_bit` — composes Campaign 1's
     `keccakf1600_eq` with Campaign 2's `bit_keccak_alg_eq` to retarget
     the impl-level `keccakf1600_post`.

  Plan: `~/.claude/plans/fancy-gliding-swan.md`, Phase 3.
-/
import LibcruxIotSha3.BitKeccak.StructEquiv
import LibcruxIotSha3.Equivalence.Keccakf1600Loop

namespace libcrux_iot_sha3.BitKeccak

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3 libcrux_iot_sha3.Equivalence

/-! ## Per-round step on `KState` (theta + pi_rho_chi_1 + pi_rho_chi_2). -/

@[inline] def bit_round0 (s : KState) : KState :=
  let s1 := bit_keccakf1600_round0_theta s
  let s2 := bit_keccakf1600_round0_pi_rho_chi_1 0#usize s1
  bit_keccakf1600_round0_pi_rho_chi_2 s2

@[inline] def bit_round1 (s : KState) : KState :=
  let s1 := bit_keccakf1600_round1_theta s
  let s2 := bit_keccakf1600_round1_pi_rho_chi_1 0#usize s1
  bit_keccakf1600_round1_pi_rho_chi_2 s2

@[inline] def bit_round2 (s : KState) : KState :=
  let s1 := bit_keccakf1600_round2_theta s
  let s2 := bit_keccakf1600_round2_pi_rho_chi_1 0#usize s1
  bit_keccakf1600_round2_pi_rho_chi_2 s2

@[inline] def bit_round3 (s : KState) : KState :=
  let s1 := bit_keccakf1600_round3_theta s
  let s2 := bit_keccakf1600_round3_pi_rho_chi_1 0#usize s1
  bit_keccakf1600_round3_pi_rho_chi_2 s2

/-- `bit_keccakf1600_4rounds 0 = bit_round3 ∘ bit_round2 ∘ bit_round1 ∘ bit_round0`. -/
theorem bit_keccakf1600_4rounds_eq_chain (s : KState) :
    bit_keccakf1600_4rounds 0#usize s
    = bit_round3 (bit_round2 (bit_round1 (bit_round0 s))) := by
  rfl

/-! ## KState ↔ state.KeccakState round-trip

    Required for the top-level composition: Campaign 1's `keccakf1600_eq`
    outputs `KState.fromAeneas r = bit_keccak_spec (KState.fromAeneas s)`,
    and Campaign 2's `bit_keccak_alg_eq` reads its input via `KState.toAeneas`.
    The bridge `KState.toAeneas (KState.fromAeneas s) = s` (for the cases
    where the input is the impl's initial state with well-formed lanes)
    closes the loop. -/

private theorem stateArray25_toAeneas_fromAeneas
    (a : Aeneas.Std.Array lane.Lane2U32 25#usize) :
    stateArray25ToAeneas (stateArray25FromAeneas a) = a := by
  obtain ⟨vals, hlen⟩ := a
  apply Subtype.ext
  show ((vals.map Lane.fromAeneas).toArray.toList.map Lane.toAeneas) = vals
  rw [List.toList_toArray, List.map_map]
  rw [show (Lane.toAeneas ∘ Lane.fromAeneas) = id from
        funext (fun l => Lane.toAeneas_fromAeneas l)]
  exact List.map_id vals

private theorem stateArray5_toAeneas_fromAeneas
    (a : Aeneas.Std.Array lane.Lane2U32 5#usize) :
    stateArray5ToAeneas (stateArray5FromAeneas a) = a := by
  obtain ⟨vals, hlen⟩ := a
  apply Subtype.ext
  show ((vals.map Lane.fromAeneas).toArray.toList.map Lane.toAeneas) = vals
  rw [List.toList_toArray, List.map_map]
  rw [show (Lane.toAeneas ∘ Lane.fromAeneas) = id from
        funext (fun l => Lane.toAeneas_fromAeneas l)]
  exact List.map_id vals

theorem KState.toAeneas_fromAeneas (s : state.KeccakState) :
    KState.toAeneas (KState.fromAeneas s) = s := by
  unfold KState.toAeneas KState.fromAeneas
  rcases s with ⟨st, c, d, i⟩
  refine state.KeccakState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, rfl⟩
  · exact stateArray25_toAeneas_fromAeneas st
  · exact stateArray5_toAeneas_fromAeneas c
  · exact stateArray5_toAeneas_fromAeneas d

/-! ## Per-round `s.i` increments on the bit side

    Each `bit_round{k}` bumps `s.i` by 1 (the `_zeta1` sub-piece in
    `pi_rho_chi_1` is the only one that increments). Used to thread the
    `s.i.val = 4 * group_idx + k` chain across the 4-round group. -/

/-- Converting `(⟨s.i.bv + 1⟩ : Std.Usize).val` to `s.i.val + 1` under
    a tame upper bound on `s.i.val`. The structural `_i` lemmas in
    `StructEquiv.lean` give the bit-side increment in `⟨_ + 1⟩` form;
    this bridges to `.val + 1` form. -/
private theorem usize_succ_val (s : Aeneas.Std.Usize) (hi : s.val < 24) :
    (⟨s.bv + (1 : BitVec System.Platform.numBits)⟩ : Aeneas.Std.Usize).val = s.val + 1 := by
  show (s.bv + (1 : BitVec System.Platform.numBits)).toNat = s.val + 1
  have h32 : (32 : Nat) ≤ System.Platform.numBits := by
    have := System.Platform.numBits_eq; omega
  have hone : (1 : BitVec System.Platform.numBits).toNat = 1 := by
    have h1 : (1 : Nat) % 2 ^ System.Platform.numBits = 1 := by
      apply Nat.mod_eq_of_lt
      have : (2 : Nat) ^ 32 ≤ 2 ^ System.Platform.numBits :=
        Nat.pow_le_pow_right (by decide) h32
      omega
    simp [BitVec.toNat_ofNat, h1]
  rw [BitVec.toNat_add, hone]
  apply Nat.mod_eq_of_lt
  have hsv : s.bv.toNat = s.val := rfl
  have : (2 : Nat) ^ 32 ≤ 2 ^ System.Platform.numBits :=
    Nat.pow_le_pow_right (by decide) h32
  rw [hsv]; omega

theorem bit_round0_i (s : KState) (hi : s.i.val < 24) :
    (bit_round0 s).i.val = s.i.val + 1 := by
  unfold bit_round0
  rw [bit_keccakf1600_round0_pi_rho_chi_2_i,
      bit_keccakf1600_round0_pi_rho_chi_1_i,
      bit_keccakf1600_round0_theta_i]
  exact usize_succ_val s.i hi

theorem bit_round1_i (s : KState) (hi : s.i.val < 24) :
    (bit_round1 s).i.val = s.i.val + 1 := by
  unfold bit_round1
  rw [bit_keccakf1600_round1_pi_rho_chi_2_i,
      bit_keccakf1600_round1_pi_rho_chi_1_i,
      bit_keccakf1600_round1_theta_i]
  exact usize_succ_val s.i hi

theorem bit_round2_i (s : KState) (hi : s.i.val < 24) :
    (bit_round2 s).i.val = s.i.val + 1 := by
  unfold bit_round2
  rw [bit_keccakf1600_round2_pi_rho_chi_2_i,
      bit_keccakf1600_round2_pi_rho_chi_1_i,
      bit_keccakf1600_round2_theta_i]
  exact usize_succ_val s.i hi

theorem bit_round3_i (s : KState) (hi : s.i.val < 24) :
    (bit_round3 s).i.val = s.i.val + 1 := by
  unfold bit_round3
  rw [bit_keccakf1600_round3_pi_rho_chi_2_i,
      bit_keccakf1600_round3_pi_rho_chi_1_i,
      bit_keccakf1600_round3_theta_i]
  exact usize_succ_val s.i hi

/-! ## Per-round algebraic correspondence (the load-bearing 4 sorries).

    Statement shape (for k ∈ {0,1,2,3}):

    `spec_round_step (lift_perm s.toAeneas (impl_perm^[k]) impl_swap) s.i`
    `  = .ok (lift_perm (bit_round{k} s).toAeneas (impl_perm^[k+1]) impl_swap)`

    The k=0 case is the bit-side analogue of `round0_equiv_spec` (already
    proven in `RoundEquiv.lean` via `theta_lift_spec + prc_lift_spec`).
    The k=1,2,3 cases are the same algebra applied at different
    impl_perm-shifted lane addressings — they transcribe the (currently
    sorry'd) `theta_lift_spec_k + prc_lift_spec_k` content but stated
    against the pure-Lean `bit_round{k}` rather than the Aeneas
    `keccakf1600_round{k}_*` chain. -/

/-- Round 0 algebraic equivalence. Algebra mirrors `theta_lift_spec +
    prc_lift_spec` from `ThetaLift.lean` + `PrcLift.lean`, transcribed
    against the pure-Lean `bit_round0` definition. -/
theorem bit_round0_alg_eq (s : KState) (hi : s.i.val < 24) :
    spec_round_step (lift_perm s.toAeneas id impl_swap) s.i
    = .ok (lift_perm (bit_round0 s).toAeneas impl_perm impl_swap) := by
  sorry

/-- Round 1 algebraic equivalence. Algebra mirrors `theta_lift_spec_1 +
    prc_lift_spec_1` (currently sorry'd in `ThetaLiftRound1.lean` +
    `PrcLiftRound1.lean`), transcribed against `bit_round1`. -/
theorem bit_round1_alg_eq (s : KState) (hi : s.i.val < 24) :
    spec_round_step (lift_perm s.toAeneas impl_perm impl_swap) s.i
    = .ok (lift_perm (bit_round1 s).toAeneas (impl_perm ∘ impl_perm) impl_swap) := by
  sorry

/-- Round 2 algebraic equivalence. Algebra mirrors `theta_lift_spec_2 +
    prc_lift_spec_2` (sorry'd in `ThetaLiftRound2.lean` +
    `PrcLiftRound2.lean`), transcribed against `bit_round2`. -/
theorem bit_round2_alg_eq (s : KState) (hi : s.i.val < 24) :
    spec_round_step (lift_perm s.toAeneas (impl_perm ∘ impl_perm) impl_swap) s.i
    = .ok (lift_perm (bit_round2 s).toAeneas (impl_perm ∘ impl_perm ∘ impl_perm) impl_swap) := by
  sorry

/-- Round 3 algebraic equivalence. After round 3, `impl_perm^[4] = id`
    collapses the permutation. Algebra mirrors `theta_lift_spec_3 +
    prc_lift_spec_3` (sorry'd in `ThetaLiftRound3.lean` +
    `PrcLiftRound3.lean`), transcribed against `bit_round3`. -/
theorem bit_round3_alg_eq (s : KState) (hi : s.i.val < 24) :
    spec_round_step (lift_perm s.toAeneas (impl_perm ∘ impl_perm ∘ impl_perm) impl_swap) s.i
    = .ok (lift_perm (bit_round3 s).toAeneas id impl_swap) := by
  sorry

/-! ## 4-round closure

    Composes the 4 per-round algebraic identities via `Result.bind`
    associativity. Uses the i-increment chain to align iota constants. -/

set_option maxHeartbeats 4000000 in
theorem bit_4rounds_alg_eq (s : KState) (hi : s.i.val + 4 ≤ 24) :
    (do
      let s1 ← spec_round_step (lift_perm s.toAeneas id impl_swap) s.i
      let s2 ← spec_round_step s1 (roundOfNat (s.i.val + 1) (by omega))
      let s3 ← spec_round_step s2 (roundOfNat (s.i.val + 2) (by omega))
      spec_round_step s3 (roundOfNat (s.i.val + 3) (by omega)))
    = .ok (lift_perm (bit_keccakf1600_4rounds 0#usize s).toAeneas id impl_swap) := by
  rw [bit_keccakf1600_4rounds_eq_chain]
  -- Round 0
  have h0 := bit_round0_alg_eq s (by omega)
  rw [h0]; simp only [Aeneas.Std.bind_tc_ok]
  -- Round 1: align iota constant via i-chain
  have h_i0_val : (bit_round0 s).i.val = s.i.val + 1 := bit_round0_i s (by omega)
  have h_i1 : (bit_round0 s).i = roundOfNat (s.i.val + 1) (by omega) := by
    apply Std.UScalar.eq_of_val_eq
    rw [h_i0_val]
    unfold roundOfNat; rw [Std.UScalar.ofNatCore_val_eq]
  have h1 := bit_round1_alg_eq (bit_round0 s) (by rw [h_i0_val]; omega)
  rw [← h_i1, h1]; simp only [Aeneas.Std.bind_tc_ok]
  -- Round 2
  have h_i1_val : (bit_round1 (bit_round0 s)).i.val = s.i.val + 2 := by
    rw [bit_round1_i _ (by rw [h_i0_val]; omega), h_i0_val]
  have h_i2 : (bit_round1 (bit_round0 s)).i = roundOfNat (s.i.val + 2) (by omega) := by
    apply Std.UScalar.eq_of_val_eq
    rw [h_i1_val]
    unfold roundOfNat; rw [Std.UScalar.ofNatCore_val_eq]
  have h2 := bit_round2_alg_eq (bit_round1 (bit_round0 s)) (by rw [h_i1_val]; omega)
  rw [← h_i2, h2]; simp only [Aeneas.Std.bind_tc_ok]
  -- Round 3
  have h_i2_val : (bit_round2 (bit_round1 (bit_round0 s))).i.val = s.i.val + 3 := by
    rw [bit_round2_i _ (by rw [h_i1_val]; omega), h_i1_val]
  have h_i3 : (bit_round2 (bit_round1 (bit_round0 s))).i = roundOfNat (s.i.val + 3) (by omega) := by
    apply Std.UScalar.eq_of_val_eq
    rw [h_i2_val]
    unfold roundOfNat; rw [Std.UScalar.ofNatCore_val_eq]
  have h3 := bit_round3_alg_eq (bit_round2 (bit_round1 (bit_round0 s))) (by rw [h_i2_val]; omega)
  rw [← h_i3, h3]

set_option maxHeartbeats 2000000 in
/-- Index-parameterized variant of `bit_4rounds_alg_eq`. Takes a `Nat`
    index `n` and the equation `n = s.i.val`; substitution then makes
    this identical in shape to `bit_4rounds_alg_eq` modulo the first
    `s.i` ↔ `roundOfNat n _` identity (closed by `Std.UScalar.eq_of_val_eq`). -/
theorem bit_4rounds_alg_eq_at (s : KState) (n : Nat) (h_n : n + 4 ≤ 24)
    (h_i : n = s.i.val) :
    (do
      let s1 ← spec_round_step (lift_perm s.toAeneas id impl_swap)
                  (roundOfNat n (by omega))
      let s2 ← spec_round_step s1 (roundOfNat (n + 1) (by omega))
      let s3 ← spec_round_step s2 (roundOfNat (n + 2) (by omega))
      spec_round_step s3 (roundOfNat (n + 3) (by omega)))
    = .ok (lift_perm (bit_keccakf1600_4rounds 0#usize s).toAeneas id impl_swap) := by
  subst h_i
  -- Indices are now `s.i.val + k`, matching bit_4rounds_alg_eq.
  have h_chain := bit_4rounds_alg_eq s h_n
  -- The only difference: goal has `roundOfNat s.i.val _` at position 0,
  -- h_chain has `s.i`. Rewrite the goal direction (not h_chain) to avoid
  -- dependent-rewrite friction on the remaining roundOfNat indices.
  have h_si_eq : roundOfNat s.i.val (by omega) = s.i := by
    apply Std.UScalar.eq_of_val_eq
    unfold roundOfNat; rw [Std.UScalar.ofNatCore_val_eq]
  rw [h_si_eq]
  exact h_chain

/-! ## i-increment for `bit_keccakf1600_4rounds` -/

theorem bit_keccakf1600_4rounds_i (s : KState) (hi : s.i.val + 4 ≤ 24) :
    (bit_keccakf1600_4rounds 0#usize s).i.val = s.i.val + 4 := by
  rw [bit_keccakf1600_4rounds_eq_chain]
  have h0 : (bit_round0 s).i.val = s.i.val + 1 := bit_round0_i s (by omega)
  have h1 : (bit_round1 (bit_round0 s)).i.val = s.i.val + 2 := by
    rw [bit_round1_i _ (by rw [h0]; omega), h0]
  have h2 : (bit_round2 (bit_round1 (bit_round0 s))).i.val = s.i.val + 3 := by
    rw [bit_round2_i _ (by rw [h1]; omega), h1]
  rw [bit_round3_i _ (by rw [h2]; omega), h2]

/-! ## 24-round closure (the Campaign 2 target)

    Induct over 6 iterations of `bit_keccakf1600_4rounds 0`, threading
    the `s.i.val = 4k` chain to align spec_round_step indices. -/

private theorem nat_iterate_i (s : KState) (h_i : s.i.val = 0) (k : Nat) (hk : k ≤ 6) :
    (Nat.iterate (bit_keccakf1600_4rounds 0#usize) k s).i.val = 4 * k := by
  induction k with
  | zero => simpa using h_i
  | succ n IH =>
    have hn : n ≤ 6 := by omega
    have hIH := IH hn
    rw [Function.iterate_succ_apply']
    rw [bit_keccakf1600_4rounds_i _ (by rw [hIH]; omega)]
    rw [hIH]; ring

set_option maxHeartbeats 4000000 in
/-- The 24-round Campaign 2 closure on the pure-Lean side. -/
theorem bit_keccak_spec_alg_eq (s : KState) (h_i : s.i = 0#usize) :
    spec_chain (lift_perm s.toAeneas id impl_swap) 24
    = .ok (lift_perm (Nat.iterate (bit_keccakf1600_4rounds 0#usize) 6 s).toAeneas id impl_swap) := by
  have h_i_val : s.i.val = 0 := by rw [h_i]; rfl
  -- Induct over k ∈ {0..6}, tracking the i counter.
  suffices h : ∀ k ≤ 6,
      spec_chain (lift_perm s.toAeneas id impl_swap) (4 * k)
      = .ok (lift_perm (Nat.iterate (bit_keccakf1600_4rounds 0#usize) k s).toAeneas id impl_swap) by
    have h6 := h 6 (by omega)
    rw [show (24 : Nat) = 4 * 6 from rfl]; exact h6
  intro k hk
  induction k with
  | zero =>
    simp only [Nat.mul_zero, spec_chain_zero, Function.iterate_zero, id_eq]
  | succ n IH =>
    have hn : n ≤ 6 := by omega
    have IH' := IH hn
    -- 4 * (n+1) = 4 * n + 4
    rw [show 4 * (n + 1) = 4 * n + 4 from by ring]
    -- spec_chain (4*n + 4) = spec_chain (4*n) >>= (4-step group)
    rw [show 4 * n + 4 = (4 * n + 3) + 1 from rfl, spec_chain_succ]
    rw [show 4 * n + 3 = (4 * n + 2) + 1 from rfl, spec_chain_succ]
    rw [show 4 * n + 2 = (4 * n + 1) + 1 from rfl, spec_chain_succ]
    rw [show 4 * n + 1 = 4 * n + 1 from rfl, spec_chain_succ]
    rw [IH']
    simp only [Aeneas.Std.bind_tc_ok]
    -- Goal: 4-step chain starting from (lift_perm (iter^[n] s) id impl_swap) at index 4*n
    --       = .ok (lift_perm (iter^[n+1] s) id impl_swap)
    rw [Function.iterate_succ_apply']
    -- Set acc := iter^[n] s and use bit_4rounds_alg_eq.
    have h_acc_i_val : (Nat.iterate (bit_keccakf1600_4rounds 0#usize) n s).i.val = 4 * n :=
      nat_iterate_i s h_i_val n hn
    have h_acc_i_bnd : (Nat.iterate (bit_keccakf1600_4rounds 0#usize) n s).i.val + 4 ≤ 24 := by
      rw [h_acc_i_val]; omega
    set acc := Nat.iterate (bit_keccakf1600_4rounds 0#usize) n s
    have h_chain := bit_4rounds_alg_eq_at acc (4 * n) (by omega) h_acc_i_val.symm
    -- Goal has spec_round_step_at; reduce to spec_round_step + roundOfNat
    -- and align do-block desugaring with bind_assoc.
    unfold spec_round_step_at
    simp only [show (4 * n + 1 + 1 : Nat) = 4 * n + 2 from rfl,
               show (4 * n + 1 + 1 + 1 : Nat) = 4 * n + 3 from rfl,
               dif_pos (show 4 * n < 24 by omega),
               dif_pos (show 4 * n + 1 < 24 by omega),
               dif_pos (show 4 * n + 2 < 24 by omega),
               dif_pos (show 4 * n + 3 < 24 by omega),
               bind_assoc]
    exact h_chain

/-! ## Top-level composition with Campaign 1

    Combines `keccakf1600_eq` (Campaign 1: impl ≡ bit_keccak_spec on
    pure-Lean side) with `bit_keccak_spec_alg_eq` (Campaign 2: 24-fold
    spec on lift_perm equals lift_perm of bit_keccak_spec) to derive
    the impl-level top-level `keccakf1600_equiv` post (with `Balanced`
    precondition via `h_lift`). -/

theorem keccakf1600_equiv_via_bit (s : state.KeccakState)
    (h_i : s.i = 0#usize)
    (h_lift : Equivalence.lift s = lift_perm s id impl_swap) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600 s
    ⦃ ⇓ r_impl => ⌜ keccakf1600_post s r_impl ⌝ ⦄ := by
  apply Std.Do.Triple.of_entails_right _ (keccakf1600_eq s h_i)
  rw [PostCond.entails_noThrow]
  intro r h_fromAeneas
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_fromAeneas ⊢
  unfold keccakf1600_post
  -- Bridge: `keccakf1600_post`'s Nat.fold IS `spec_chain` (it's just inlined).
  -- (`keccakf1600_loop_post_eq_spec_chain` formalizes this for `_loop_post`;
  -- the same proof works here.)
  have h_post_eq :
      (do let lifted_final ← Nat.fold 24
            (fun i h acc => acc >>= fun st => spec_round_step st (roundOfNat i (by omega)))
            (pure (Equivalence.lift s))
          pure (lifted_final = lift_perm r id impl_swap)).holds
      = (do let lifted_final ← spec_chain (Equivalence.lift s) 24
            pure (lifted_final = lift_perm r id impl_swap)).holds := by
    unfold spec_chain spec_round_step_at
    congr 1
  rw [h_post_eq]
  -- Bridge lift s → lift_perm s id impl_swap (h_lift) → lift_perm (toAeneas (fromAeneas s)) id impl_swap.
  rw [h_lift, show lift_perm s id impl_swap
                = lift_perm (KState.toAeneas (KState.fromAeneas s)) id impl_swap from by
        rw [KState.toAeneas_fromAeneas]]
  -- Apply Campaign 2.
  have h_i' : (KState.fromAeneas s).i = 0#usize := by
    show (KState.fromAeneas s).i = 0#usize
    unfold KState.fromAeneas
    exact h_i
  rw [bit_keccak_spec_alg_eq (KState.fromAeneas s) h_i']
  unfold bit_keccak_spec at h_fromAeneas
  -- Bridge: r.st = (toAeneas (iter^[6] (fromAeneas s))).st (since lift_perm
  -- reads only .st, and `with i := 0` preserves `.st` on both sides).
  have h_lift_perm_st_only :
      ∀ (a b : state.KeccakState), a.st = b.st →
        lift_perm a id impl_swap = lift_perm b id impl_swap := by
    intro a b hab
    unfold lift_perm
    apply Subtype.ext
    show List.ofFn (fun i : Fin 25 => lift_lane_maybe_swap (a.st.val[(id i).val]!) (impl_swap (id i)))
       = List.ofFn (fun i : Fin 25 => lift_lane_maybe_swap (b.st.val[(id i).val]!) (impl_swap (id i)))
    rw [hab]
  have h_r_eq_iter_st :
      r.st = (KState.toAeneas
                (Nat.iterate (bit_keccakf1600_4rounds 0#usize) 6 (KState.fromAeneas s))).st := by
    -- r.st = toAeneas (fromAeneas r).st (round-trip on .st)
    have hrt : r.st = stateArray25ToAeneas (KState.fromAeneas r).st :=
      (stateArray25_toAeneas_fromAeneas r.st).symm
    rw [hrt]
    -- (fromAeneas r).st = (iter^[6] _).st (from h_fromAeneas; `with i := 0` keeps `.st`)
    have h_from_st : (KState.fromAeneas r).st
                   = (Nat.iterate (bit_keccakf1600_4rounds 0#usize) 6 (KState.fromAeneas s)).st := by
      rw [h_fromAeneas]
    rw [h_from_st]
    rfl
  apply pure_prop_holds
  exact h_lift_perm_st_only _ _ h_r_eq_iter_st.symm

end libcrux_iot_sha3.BitKeccak
