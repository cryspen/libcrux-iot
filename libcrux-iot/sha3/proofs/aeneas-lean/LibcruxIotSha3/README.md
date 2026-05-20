# SHA-3 Keccak-f[1600] impl ↔ spec equivalence

This tree contains the Lean 4 proof that the bit-interleaved Rust
implementation of Keccak-f[1600] in `libcrux-iot/sha3/src/` computes
the same function as the FIPS-202 / hacspec specification in
`specs/sha3/src/`. Both sides are auto-extracted via the
[hax → aeneas → aeneas-lean](https://github.com/AeneasVerif/aeneas)
pipeline; this directory then proves their equivalence.

For the extraction pipeline + per-file build commands, see
[`Equivalence/README.md`](Equivalence/README.md).

## Main theorem

[`Equivalence/HacspecBridge.lean:1257`](Equivalence/HacspecBridge.lean#L1257):

```lean
theorem keccakf1600_equiv_hacspec (s : state.KeccakState)
    (h_i : s.i = 0#usize) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600 s
    ⦃ ⇓ r_impl => ⌜ keccak_f.keccak_f (lift s) = .ok (lift r_impl) ⌝ ⦄
```

Informally: the impl's 24-round Keccak-f[1600] permutation, lifted
to the spec's flat-`u64[25]` representation, equals what the hacspec
top-level `keccak_f.keccak_f` (defined in `specs/sha3/src/keccak_f.rs`,
extracted to `HacspecSha3/Extraction/Funs.lean`) produces when applied
to the same lifted input. Only standard Lean axioms (`propext`,
`Classical.choice`, `Quot.sound`) plus `Lean.ofReduceBool` /
`Lean.trustCompiler` inherited transitively from a single
`native_decide` in [`Equivalence/RcEquiv.lean:29`](Equivalence/RcEquiv.lean#L29)
(24-entry round-constant identity check under `@[irreducible]` arrays).

## Underlying bit-interleaved post

[`BitKeccak/AlgEquiv.lean:617`](BitKeccak/AlgEquiv.lean#L617):

```lean
theorem keccakf1600_equiv_via_bit (s : state.KeccakState)
    (h_i : s.i = 0#usize) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600 s
    ⦃ ⇓ r_impl => ⌜ keccakf1600_post_canonical s r_impl ⌝ ⦄
```

where ([`Equivalence/Keccakf1600.lean`](Equivalence/Keccakf1600.lean))

```lean
def keccakf1600_post_canonical (s r_impl : state.KeccakState) : Prop :=
  (do let lifted_final ← Nat.fold 24 (fun i _ acc =>
        acc >>= fun st => spec_round_step st (roundOfNat i ...))
        (pure (lift s))
      pure (lifted_final = lift r_impl)).holds
```

The bit-interleaved post characterises the impl through the
`_unrolled` spec chain. The hacspec-level theorem composes this with
`spec_chain_hacspec_eq_spec_chain` (Bridge 1's loop-body equivalence:
non-`_unrolled` hacspec functions equal their `_unrolled` counterparts)
and `keccak_f_loop_eq_spec_chain_hacspec` (24-step unroll of the
hacspec loop into `Nat.fold`).

## Proof architecture

The two sides represent state differently. **Spec**: 25 lanes of
`u64`. **Impl**: 25 lanes split into bit-interleaved 32-bit half
pairs `(z0, z1)` (so 64-bit rotations on 32-bit targets reduce to
32-bit rotations + half-swaps). Additionally, the impl uses storage
relabeling for π: each round reads from a different physical layout.
The relabeling permutation `impl_perm : Fin 25 → Fin 25` has order 4.

The bridge `lift : KeccakState → Array u64 25` (in
[`Equivalence/Lift.lean`](Equivalence/Lift.lean)) interleaves halves
back into `u64`s. A generalised `lift_perm s p sw` reads each lane
through a permutation `p` and an optional half-swap `sw` (`Fin 25 → Bool`).

### Two campaigns

The proof factors through a **pure-Lean intermediate spec**
`bit_keccak_spec : KState → KState` (in [`BitKeccak/Spec.lean`](BitKeccak/Spec.lean))
that mirrors the impl's bit-side data flow without the Aeneas monad:

1. **Campaign 1** (impl ↔ `bit_keccak_spec`) — proves the Rust
   extraction equals the pure-Lean bit spec under `KState.fromAeneas`.
   See `BitKeccak/StructEquiv.lean`. ~3000 lines, no algebraic
   reasoning; mostly mvcgen.

2. **Campaign 2** (`bit_keccak_spec` ↔ hacspec) — proves the pure-Lean
   bit spec, lifted to `u64`, equals the hacspec round application.
   This is the algebraic content. See `BitKeccak/AlgEquiv.lean` and the
   per-round files in `Equivalence/`.

The top-level theorem composes them at the end of `AlgEquiv.lean`.

### Time-varying polarity (the load-bearing architectural pivot)

Campaign 2's per-round identities use a time-varying half-swap
function `impl_swap_k : Nat → Fin 25 → Bool` with a 4-cycle:
`impl_swap_k 0 = swZero`, `impl_swap_k 1 = impl_swap`, `impl_swap_k 2`
and `impl_swap_k 3` track intermediate polarities, `impl_swap_k 4 =
impl_swap_k 0`. Both ends of each 4-round chunk land on `swZero`, so
the canonical `lift` threads through the 24-round chain
unconditionally. An earlier attempt used a `BalancedAt` precondition;
it was abandoned after empirical evidence that `Balanced` is not
preserved across rounds 1–3.

### Per-round building blocks

For each round `k ∈ {0, 1, 2, 3}`:

- `theta_lift_spec_k` — the impl's θ step produces a state whose lift
  matches the spec's `theta_unrolled` of the perm/swap-aware input.
- `prc_lift_spec_k` — the impl's `pi_rho_chi_1 ; pi_rho_chi_2` step,
  combined with iota, matches the spec's `ρ ∘ π ∘ χ ∘ ι`.
- `round_k_equiv_spec` — composes the two via `mvcgen` on
  `round_k_post`.
- `bit_round_k_alg_eq` — the algebraic identity `spec_round_step (lift_perm
  s ...) s.i = .ok (lift_perm (bit_round_k s) ...)`.

Round 0 is the baseline (uses canonical `lift`, `impl_swap_k 0 = swZero`,
no permutation). Rounds 1, 2, 3 mirror the same architecture with
`(impl_perm^k, impl_swap_k k)` parameters.

`bit_4rounds_alg_eq` composes the four `bit_round_k_alg_eq`s via
`Result.bind`. `bit_keccak_spec_alg_eq` iterates that 6 times to cover
24 rounds.

## File map

```
LibcruxIotSha3/
├── README.md                        ← you are here
│
├── BitKeccak/                       ← pure-Lean bit-keccak intermediate spec
│   ├── State.lean                   ← KState definition (pure-Lean version of
│   │                                  state.KeccakState)
│   ├── StateIso.lean                ← KState ↔ state.KeccakState round-trips
│   ├── Spec.lean                    ← bit_keccak_spec + bit_round_k pure-Lean step
│   │                                  functions (bit_round0, ..., bit_round3)
│   ├── Project.lean                 ← projections / accessors
│   ├── StructEquiv.lean             ← Campaign 1: impl ≡ bit_keccak_spec
│   │                                  via mvcgen + structural induction (~3000 LOC)
│   └── AlgEquiv.lean                ← Campaign 2 finale: bit_round_k_alg_eq
│                                      + bit_4rounds_alg_eq + bit_keccak_spec_alg_eq
│                                      + keccakf1600_equiv_via_bit (top theorem)
│
├── Equivalence/                     ← algebraic infrastructure for Campaign 2
│   ├── README.md                    ← extraction pipeline + build/iteration tips
│   │
│   ├── Lift.lean                    ← lift_lane_bv, lift, lift_perm, impl_perm,
│   │                                  impl_swap, impl_swap_k + 4-cycle lemmas,
│   │                                  lift_lane_maybe_swap_{true,false}_bv,
│   │                                  rotateLeft1_xor_bv32, generic lift_perm_getElem
│   ├── UScalarAC.lean               ← Std.Associative / Std.Commutative instances
│   │                                  for Std.UScalar.xor/and/or (Aeneas surface fill)
│   ├── RcEquiv.lean                 ← rc_equiv: bit-interleaved round constants
│   │                                  match the spec's ROUND_CONSTANTS
│   ├── I32LoopSpec.lean             ← I32 iterator + loop_range_spec_i32 (used by
│   │                                  StructEquiv's 6-iteration loop spec)
│   ├── SpecChain.lean               ← spec_round_step_at + spec_chain (Nat.fold
│   │                                  wrapper) + pure_prop_holds helpers
│   ├── StepSpecs.lean               ← preservation specs for impl rounds 1–3
│   │                                  (82 declarations via step_preserve_proof macro)
│   │
│   ├── ThetaLiftDefs.lean           ← 11 round-0 θ sub-fn @[spec]s
│   │                                  + theta_comp_spec_local
│   │                                  + lift_theta_applied(_perm) definitions
│   │                                  + theta_c_proof macro (reused by rounds 1–3)
│   ├── ThetaLift.lean               ← round-0 theta_lift_spec
│   ├── ThetaLiftRound1.lean         ← round-1 11 sub-fn @[spec]s + 25 lta_perm_bv_*_1
│   ├── ThetaLiftRound2.lean         ← round-2 analog
│   ├── ThetaLiftRound3.lean         ← round-3 analog
│   │
│   ├── PrcLift.lean                 ← 10 round-0 πρχι sub-fn @[spec]s
│   │                                  + prc_y_zeta_no_rc_proof macro (reused)
│   │                                  + prc_lift_spec (round 0)
│   ├── PrcLiftRound1.lean           ← round-1 10 sub-fn @[spec]s + 25 input lemmas
│   │                                  + prc_lift_spec_1 (uses prc_spec shared across rounds)
│   ├── PrcLiftRound2.lean           ← round-2 analog
│   ├── PrcLiftRound3.lean           ← round-3 analog
│   │
│   ├── RoundEquiv.lean              ← round_k_equiv_spec for k=0,1,2,3 + per-round
│   │                                  i-increment lemmas + chain wrappers
│   ├── Keccakf1600.lean             ← keccakf1600_post + keccakf1600_post_canonical
│   │                                  definitions (the public post shapes)
│   ├── SpecChain.lean               ← spec_chain over _unrolled functions
│   └── HacspecBridge.lean           ← Bridge 1: hacspec coupling. createi_pure_spec,
│                                      6 per-closure [spec] Triples, 4 function
│                                      equalities keccak_f.X = keccak_f.X_unrolled,
│                                      spec_chain_hacspec_eq_spec_chain, Usize
│                                      iterator/loop specs, keccak_f_loop_eq_*,
│                                      and the top theorem keccakf1600_equiv_hacspec
│
└── Extraction/
    ├── Funs.lean                    ← Rust impl extraction (generated; do not edit)
    └── Missing.lean                 ← hand-written aeneas surface fills
```

## Verifying

From `libcrux-iot/sha3/proofs/aeneas-lean/`:

```bash
lake exe cache get        # one-time prime
lake build LibcruxIotSha3.Equivalence.HacspecBridge   # final hacspec coupling
# or LibcruxIotSha3.BitKeccak.AlgEquiv for the bit-interleaved post only
```

Expected: 0 sorries in `LibcruxIotSha3/`, only standard Lean axioms.
`keccakf1600_equiv_hacspec` and `keccakf1600_equiv_via_bit` both
report `propext` + `Classical.choice` + `Quot.sound` + `Lean.ofReduceBool`
+ `Lean.trustCompiler`. The non-standard `Lean.ofReduceBool`/
`Lean.trustCompiler` come from a single `native_decide` in
`Equivalence/RcEquiv.lean:29` (24-entry round-constant identity check)
needed because the round-constant arrays are `@[irreducible]`.

```bash
grep -rn "by sorry\|^  sorry" LibcruxIotSha3/   # must be empty
```

## See also

- [`Equivalence/README.md`](Equivalence/README.md) — extraction pipeline,
  per-file build/iteration tips, re-extraction commands.
- `Plan: ~/.claude/plans/fancy-gliding-swan.md` (referenced from
  `BitKeccak/AlgEquiv.lean`) — historical plan; partially outdated.
