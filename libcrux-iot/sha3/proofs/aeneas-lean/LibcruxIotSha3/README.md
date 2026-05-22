# SHA-3 Keccak-f[1600] impl ↔ spec equivalence

This tree contains the Lean 4 proof that the bit-interleaved Rust
implementation of Keccak-f[1600] in `libcrux-iot/sha3/src/` computes
the same function as the FIPS-202 / hacspec specification in
`specs/sha3/src/`. Both sides are auto-extracted via the
[hax → aeneas → aeneas-lean](https://github.com/AeneasVerif/aeneas)
pipeline; this directory then proves their equivalence.

For the extraction pipeline + per-file build commands, see
[`Equivalence/README.md`](Equivalence/README.md).

## Main theorems

There are two layers of top theorem:

### Layer 1 — Keccak-f[1600] permutation equivalence (Bridge 1)

[`Composition/HacspecBridge.lean`](Composition/HacspecBridge.lean):

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
to the same lifted input.

### Layer 2 — full sponge (SHA-3 / SHAKE) equivalence (Campaign 3)

[`Sponge/Sha3.lean`](Sponge/Sha3.lean) — `keccak.keccak_keccak_spec`:

```lean
theorem keccak.keccak_keccak_spec
    (RATE : Std.Usize) (DELIM : Std.U8)
    (data : Slice Std.U8) (out : Slice Std.U8)
    (h_RATE_mod : RATE.val % 8 = 0)
    (h_RATE_ge_1 : 1 ≤ RATE.val)
    (h_RATE_le_200 : RATE.val ≤ 200) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccak RATE DELIM data out
    ⦃ ⇓ r => ⌜ ∃ spec_out : Std.Array Std.U8 (Std.Slice.len out),
                sponge.keccak (Std.Slice.len out) RATE DELIM data
                  = .ok spec_out
                ∧ r.val.length = out.val.length
                ∧ ∀ k : Nat, k < out.val.length →
                    r.val[k]! = spec_out.val[k]! ⌝ ⦄
```

Informally: the generic SHA-3 sponge driver `keccak.keccak` (rate `RATE`,
delimiter `DELIM`, input `data`, output buffer `out`) produces the same
byte sequence as the hacspec `sponge.keccak`. Direct corollaries
([`Sponge/Shake.lean`](Sponge/Shake.lean)):

- `shake128_spec`  — RATE 168, DELIM 0x1f.
- `shake256_spec`  — RATE 136, DELIM 0x1f.
- `sha224_ema_spec` — RATE 144, DELIM 0x06, 28-byte digest.
- `sha256_ema_spec` — RATE 136, DELIM 0x06, 32-byte digest.
- `sha384_ema_spec` — RATE 104, DELIM 0x06, 48-byte digest.
- `sha512_ema_spec` — RATE  72, DELIM 0x06, 64-byte digest.

### Axiom hygiene

Both layers' top theorems report only standard Lean axioms (`propext`,
`Classical.choice`, `Quot.sound`) plus `Lean.ofReduceBool` /
`Lean.trustCompiler` inherited transitively from a single
`native_decide` in
[`Foundation/RcEquiv.lean`](Foundation/RcEquiv.lean) (24-entry
round-constant identity check under `@[irreducible]` arrays).

## Proof architecture

The two sides represent state differently. **Spec**: 25 lanes of
`u64`. **Impl**: 25 lanes split into bit-interleaved 32-bit half
pairs `(z0, z1)` (so 64-bit rotations on 32-bit targets reduce to
32-bit rotations + half-swaps). Additionally, the impl uses storage
relabeling for π: each round reads from a different physical layout.
The relabeling permutation `impl_perm : Fin 25 → Fin 25` has order 4.

The bridge `lift : KeccakState → Array u64 25` (in
[`Foundation/Lift.lean`](Foundation/Lift.lean)) interleaves halves
back into `u64`s. A generalised `lift_perm s p sw` reads each lane
through a permutation `p` and an optional half-swap `sw : Fin 25 → Bool`.

The proof factors through a **pure-Lean intermediate spec**
`bit_keccak_spec : KState → KState` (in
[`BitSpec/Spec.lean`](BitSpec/Spec.lean)) that mirrors the impl's
bit-side data flow without the Aeneas monad. The chain of theorems
runs:

```
              StructuralEquiv          AlgebraicEquiv          Composition.HacspecBridge
impl ─────────────────────→ bit_keccak_spec ──────→ spec_chain (lift s) 24 ─────→ keccak_f.keccak_f (lift s)
   keccakf1600_eq               bit_keccak_spec_alg_eq          spec_chain_hacspec_eq_spec_chain
   (mvcgen + structural)        (algebraic, lift-aware)         + keccak_f_loop_eq_spec_chain_hacspec
                            \____________________________/
                             Composition/ViaBit.lean
                          (keccakf1600_equiv_via_bit)
```

Three named pieces (one file each at the top of the proof tree):

- **`StructuralEquiv.lean`** (impl ≡ `bit_keccak_spec`). Proves the
  Rust extraction equals the pure-Lean bit spec under
  `KState.fromAeneas`. ~3700 lines, no algebraic reasoning; mostly
  `mvcgen` + structural induction.

- **`AlgebraicEquiv.lean`** (`bit_keccak_spec` lifted ≡ hacspec
  unrolled chain). Proves the pure-Lean bit spec, lifted to `u64`,
  equals the spec round application. Per-round identities
  `bit_round{k}_alg_eq` compose into the 24-round
  `bit_keccak_spec_alg_eq`. This is the algebraic content
  (`lift_lane_bv`, `impl_perm`, `impl_swap_k` cycle).

- **`Composition/`**:
  - **`ViaBit.lean`** — composes the two equivalences above to
    produce a Triple on `keccak.keccakf1600` with post against
    `spec_round_step` iterated 24 times.
  - **`HacspecBridge.lean`** — couples the `_unrolled` spec functions
    to the non-`_unrolled` hacspec top-level `keccak_f.keccak_f` and
    its `Usize` loop, then composes with `ViaBit` to yield the top
    theorem `keccakf1600_equiv_hacspec`.

### Time-varying polarity (the load-bearing architectural pivot)

`AlgebraicEquiv`'s per-round identities use a time-varying half-swap
function `impl_swap_k : Nat → Fin 25 → Bool` with a 4-cycle:
`impl_swap_k 0 = swZero`, `impl_swap_k 1 = impl_swap`, `impl_swap_k 2`
and `impl_swap_k 3` track intermediate polarities, `impl_swap_k 4 =
impl_swap_k 0`. Both ends of each 4-round chunk land on `swZero`, so
the canonical `lift` threads through the 24-round chain
unconditionally. An earlier attempt used a `BalancedAt` precondition;
it was abandoned after empirical evidence that `Balanced` is not
preserved across rounds 1–3.

## File map

```
LibcruxIotSha3/
├── README.md                    ← you are here
│
├── Foundation/                  ← shared infrastructure (used by all three
│   │                              of StructuralEquiv, AlgebraicEquiv,
│   │                              Composition)
│   ├── Lift.lean                ← lift_lane_bv, lift, lift_perm, impl_perm,
│   │                              impl_swap, impl_swap_k + 4-cycle lemmas,
│   │                              ~40 bv_decide-closed `rot_N` lemmas
│   ├── UScalarAC.lean           ← Std.Associative/Commutative on
│   │                              Std.UScalar.xor/and/or (Aeneas surface fill)
│   ├── RcEquiv.lean             ← rc_equiv: bit-interleaved round constants
│   │                              match the spec's ROUND_CONSTANTS
│   ├── SpecStep.lean            ← spec_round_step, roundOfNat,
│   │                              keccakf1600_post_canonical, holds_chain_eq_ok
│   ├── SpecChain.lean           ← spec_chain Nat.fold wrapper + helpers
│   ├── I32LoopSpec.lean         ← I32 iterator + loop_range_spec_i32
│   ├── ThetaLiftDefs.lean       ← 11 round-0 θ sub-fn @[spec]s
│   │                              + theta_comp_spec_local
│   │                              + lift_theta_applied(_perm) defs
│   │                              + theta_c_proof macro
│   ├── ThetaLift.lean           ← round-0 theta_lift_spec
│   ├── ThetaLiftRound{1,2,3}.lean ← per-round θ specs
│   ├── PrcLift.lean             ← 10 round-0 πρχι sub-fn @[spec]s
│   │                              + prc_y_zeta_no_rc_proof macro
│   │                              + prc_lift_spec
│   ├── PrcLiftRound{1,2,3}.lean ← per-round πρχι specs
│   └── RoundEquiv.lean          ← round_k_equiv_spec for k=0..3 +
│                                  triple combinators
│
├── BitSpec/                     ← pure-Lean intermediate spec (defs only)
│   ├── State.lean               ← KState
│   ├── StateIso.lean            ← KState ↔ state.KeccakState round-trips
│   ├── Project.lean             ← projections / accessors
│   └── Spec.lean                ← bit_keccak_spec + bit_keccakf1600_*
│                                  pure-Lean step functions
│
├── StructuralEquiv.lean         ← impl ≡ bit_keccak_spec (via mvcgen +
│                                  structural induction, ~3700 LOC)
│
├── AlgebraicEquiv.lean          ← bit_round_k_alg_eq + bit_4rounds_alg_eq
│                                  + bit_keccak_spec_alg_eq (24-round closure)
│
├── Composition/                 ← composition of the two equivalences
│   ├── ViaBit.lean              ← keccakf1600_equiv_via_bit (StructuralEquiv
│   │                              ∘ AlgebraicEquiv) — Triple on the impl
│   └── HacspecBridge.lean       ← hacspec coupling: createi_pure_spec,
│                                  per-closure [spec] Triples, four
│                                  keccak_f.X = keccak_f.X_unrolled equalities,
│                                  spec_chain_hacspec_eq_spec_chain, Usize
│                                  iterator/loop specs, keccak_f_loop_eq_*,
│                                  and the top theorem keccakf1600_equiv_hacspec
│
├── Sponge/                          ← Campaign 3: SHA-3 sponge / SHAKE / SHA3-ema
│   ├── Opaque.lean                  ← § 0: keccakf1600_seal_spec (seals
│   │                                  keccakf1600 + keccak_f.keccak_f
│   │                                  [local irreducible] for the rest of Sponge)
│   ├── SliceSpecs.lean              ← Aeneas Std @[spec] bridges: Slice.len,
│   │                                  massert, slice/array indexing over Range,
│   │                                  U32/U64 LE byte conversions, try_from,
│   │                                  Result.unwrap, copy_from_slice (~12 Triples)
│   ├── Interleave.lean              ← BV-pure identities (interleave_bv,
│   │                                  deinterleave_bv, lift_lane_bv_xor) +
│   │                                  Aeneas-Result lifts of Lane2U32.{de,}interleave
│   ├── LoopSpecs.lean               ← 3 outer-fixpoint loop Triples with
│   │                                  fold-form invariants: load_block_2u32_loop{0,1},
│   │                                  store_block_2u32_loop
│   ├── Bytes.lean                   ← § 1: load_block / store_block /
│   │                                  load_block_full @[spec]s (byte ↔ lane bridge)
│   ├── XorBlockSpec.lean            ← from_fn_pure_spec (FnMut analog of
│   │                                  createi_pure_spec) + sponge.xor_block_into_state
│   │                                  per-cell + direct @[spec]
│   ├── AbsorbBlock.lean             ← § 2: keccak.absorb_block ↔ sponge.absorb_block
│   ├── Absorb.lean                  ← § 3: keccak.keccak_loop0_spec (absorb loop),
│   │                                  sponge_absorb_rec_unfold + eq_fold pure lemmas
│   ├── SqueezeBlock.lean            ← § 4: 4 squeeze block Triples
│   │                                  (squeeze_{first_block, next_block,
│   │                                   last, first_and_last}_spec)
│   ├── Squeeze.lean                 ← § 5: keccak.keccak_loop1_invariant
│   │                                  (squeeze loop with per-byte invariant),
│   │                                  iterate_keccak_f_eq_fold,
│   │                                  sponge_squeeze_byte_eq (block-wise factor)
│   ├── AbsorbFinal.lean             ← § 6: keccak.absorb_final ↔ sponge.absorb_final
│   ├── Sha3.lean                    ← § 7: keccak.keccak_keccak_spec
│   │                                  (the top sponge theorem; case-splits on
│   │                                   blocks=0 vs blocks≥1)
│   └── Shake.lean                   ← § 8: shake128/256_spec + sha{224,256,384,512}_ema_spec
│                                      (direct instantiations of keccak_keccak_spec)
│
└── Extraction/
    ├── Funs.lean                ← Rust impl extraction (generated; do not edit)
    └── Missing.lean             ← hand-written aeneas surface fills
```

### Namespaces

| Directory                | Namespace                            |
|--------------------------|--------------------------------------|
| `Foundation/`            | `libcrux_iot_sha3.Foundation`        |
| `BitSpec/`               | `libcrux_iot_sha3.BitSpec`           |
| `StructuralEquiv.lean`   | `libcrux_iot_sha3.Structural`        |
| `AlgebraicEquiv.lean`    | `libcrux_iot_sha3.Algebraic`         |
| `Composition/`           | `libcrux_iot_sha3.Composition`       |

## Verifying

From `libcrux-iot/sha3/proofs/aeneas-lean/`:

```bash
lake exe cache get        # one-time prime
lake build LibcruxIotSha3.Sponge.Shake               # final SHAKE/SHA3 ema specs
# or LibcruxIotSha3.Sponge.Sha3 for the generic keccak_keccak_spec
# or LibcruxIotSha3.Equivalence.HacspecBridge for the Bridge-1 layer only
# or LibcruxIotSha3.BitKeccak.AlgEquiv for the bit-interleaved post only
```

Expected: 0 sorries in `LibcruxIotSha3/`, only standard Lean axioms.
`keccakf1600_equiv_hacspec`, `keccakf1600_equiv_via_bit`,
`keccak.keccak_keccak_spec`, `shake128_spec`, `shake256_spec`,
`sha{224,256,384,512}_ema_spec` all report `propext` + `Classical.choice` +
`Quot.sound` + `Lean.ofReduceBool` + `Lean.trustCompiler`. The non-standard
`Lean.ofReduceBool`/`Lean.trustCompiler` come from a single `native_decide` in
`Equivalence/RcEquiv.lean:29` (24-entry round-constant identity check)
needed because the round-constant arrays are `@[irreducible]`.

```bash
grep -rn "by sorry\|^  sorry" LibcruxIotSha3/   # must be empty
```

## See also

- [`Foundation/README.md`](Foundation/README.md) — extraction pipeline
  and per-file iteration tips.
