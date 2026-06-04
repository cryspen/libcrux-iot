# SHA-3 Verification

This directory contains the Lean 4 proof that the IOT-friendly
implementation of SHA-3 in `libcrux-iot/sha3/src/` computes
the same function as the hacspec-style FIPS-202 specification in
`specs/sha3/src/`. Both sides are extracted from Rust into Lean
via the `cargo hax into aeneas-lean` pipeline. Most of the verification
code is AI-generated.

## Main theorems

The top-level results are the Keccak equivalence theorem and its corollaries, 
which state equivalence of the SHA-3 and SHAKE functions. The Keccak
equivalence is stated as follows:

[`Sponge/Keccak.lean`](Sponge/Keccak.lean) — `keccak.keccak_keccak_spec`:

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

Informally: the IOT-friendly implementation `keccak.keccak` (for some rate `RATE`,
delimiter `DELIM`, input `data`, output buffer `out`) produces the same
byte sequence as the hacspec-style specification `sponge.keccak`.

From this theorem, we can derive equivalence theorems for the SHA-3 and SHAKE functions
([`Sponge/Shake.lean`](Sponge/Shake.lean)):

- `shake128_spec`  — RATE 168, DELIM 0x1f.
- `shake256_spec`  — RATE 136, DELIM 0x1f.
- `sha224_ema_spec` — RATE 144, DELIM 0x06, 28-byte digest.
- `sha256_ema_spec` — RATE 136, DELIM 0x06, 32-byte digest.
- `sha384_ema_spec` — RATE 104, DELIM 0x06, 48-byte digest.
- `sha512_ema_spec` — RATE  72, DELIM 0x06, 64-byte digest.

The incremental API is not part of this verification.

### Axiom hygiene

All of the top-level theorems report only standard Lean axioms (`propext`,
`Classical.choice`, `Quot.sound`) plus `Lean.ofReduceBool` /
`Lean.trustCompiler`  from bv_decide (used for bitvector rotation/XOR identities
in [Foundation/Lift.lean](Foundation/Lift.lean) and related files), and from a
single native_decide in [Foundation/RcEquiv.lean](Foundation/RcEquiv.lean).


## Proof architecture

The proof has two major stages: first establishing Keccak-f[1600]
permutation equivalence as a central intermediate result, then building
the full sponge construction on top of it.

### Keccak-f[1600] permutation equivalence

[`Composition/HacspecBridge.lean`](Composition/HacspecBridge.lean):

```lean
theorem keccakf1600_equiv_hacspec (s : state.KeccakState)
    (h_i : s.i = 0#usize) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600 s
    ⦃ ⇓ r_impl => ⌜ keccak_f.keccak_f (lift s) = .ok (lift r_impl) ⌝ ⦄
```

Informally: the implementation's `keccak.keccakf1600` result, lifted
to the specification's state representation, equals what the specification's
`keccak_f.keccak_f` produces when applied to the same lifted input.

The two sides represent state differently. **Spec**: 25 lanes of
`u64`. **Impl**: 25 lanes split into bit-interleaved 32-bit half
pairs. Additionally, the impl uses storage
relabeling for π: each round reads from a different physical layout.

Each impl round is split into 11 θ sub-functions
(`theta_c_x{0..4}_z{0,1}` and `theta_d`), a `pi_rho_chi_1` (handles
rows y=0,1 plus the ι constant XOR), and a `pi_rho_chi_2` (rows
y=2,3,4). The π step is implemented as a *storage relabeling* — each
round reads lanes from different physical positions — so after one
round the canonical `5*x + y` mapping no longer holds. The relabeling
has order 4 (`impl_perm⁴ = id`), so every 4 rounds the layout
re-aligns with the spec. The full 24 rounds factor as 6 bundles of 4.

The bridge `lift : KeccakState → Array u64 25` (in
[`Foundation/Lift.lean`](Foundation/Lift.lean)) interleaves halves
back into `u64`s. A generalised `lift_perm s p sw` reads each lane
through a permutation `p` and an optional half-swap `sw : Fin 25 → Bool`.

The proof factors through a **pure-Lean intermediate spec**
`bit_keccak_spec : KState → KState` (in
[`BitSpec/Spec.lean`](BitSpec/Spec.lean)) that mirrors the impl's
bit-side data flow without the Aeneas monad.

Three named pieces (one file each at the top of the proof tree):

- **`StructuralEquiv.lean`** (impl ≡ `bit_keccak_spec`). Proves the
  Rust extraction equals the pure-Lean bit spec under
  `KState.fromAeneas`.

- **`AlgebraicEquiv.lean`** (`bit_keccak_spec` lifted ≡ unrolled version
  of spec). Proves the pure-Lean bit spec, lifted to `u64`, equals the
  unrolled version of the spec.

- **`Composition/`**:
  - **`ViaBit.lean`** — composes the two equivalences above to
    show that the impl is equivalent to the unrolled version of the spec.
  - **`HacspecBridge.lean`** — couples the `_unrolled` spec functions
    to the non-`_unrolled` spec functions to yield `keccakf1600_equiv_hacspec`
    as stated above.

### Sponge construction proof

The sponge proof ([`Sponge/`](Sponge/)) builds on `keccakf1600_equiv_hacspec`
and proceeds as follows:

- **Opacity** ([`Sponge/Opaque.lean`](Sponge/Opaque.lean)):
  seals both `keccakf1600` and `keccak_f.keccak_f` as `[local irreducible]`
  so that later sponge reasoning cannot unfold the permutation internals
  and must reason about it only via `keccakf1600_equiv_hacspec`.

- **Byte ↔ lane bridge**
  ([`Sponge/Bytes.lean`](Sponge/Bytes.lean),
  [`Sponge/AbsorbBlock.lean`](Sponge/AbsorbBlock.lean)):
  establishes that `load_block` / `store_block` correctly convert between
  the byte-oriented sponge state and the impl's bit-interleaved lane
  representation, and that `absorb_block` on the impl side matches
  `sponge.absorb_block` on the spec side.

- **Absorb loop** ([`Sponge/Absorb.lean`](Sponge/Absorb.lean)):
  proves the absorb phase loop (`keccak_loop0`) matches
  `sponge.absorb` unfolded as a pure fold over input blocks.

- **Squeeze**
  ([`Sponge/SqueezeBlock.lean`](Sponge/SqueezeBlock.lean),
  [`Sponge/Squeeze.lean`](Sponge/Squeeze.lean)):
  covers the four cases of squeeze blocks (first-only, first, next,
  last) and the squeeze loop (`keccak_loop1`) with a per-byte loop
  invariant. The key lemma `iterate_keccak_f_eq_fold` lifts the
  single-permutation result into repeated applications across blocks.

- **Final absorb** ([`Sponge/AbsorbFinal.lean`](Sponge/AbsorbFinal.lean)):
  proves `absorb_final` (padding + final permutation call) matches
  `sponge.absorb_final`.

- **Keccak** ([`Sponge/Keccak.lean`](Sponge/Keccak.lean)):
  assembles the absorb and squeeze stages into `keccak.keccak_keccak_spec`,
  case-splitting on whether there are zero or at least one full input blocks.

- **Corollaries** ([`Sponge/Shake.lean`](Sponge/Shake.lean)):
  instantiates `keccak_keccak_spec` at concrete `(RATE, DELIM)` pairs to
  yield `shake128_spec`, `shake256_spec`, and the SHA3-ema variants.


## Extraction pipeline

The specification and the implementation are extracted separately, 
using the python scripts [`libcrux-iot/sha3/hax_aeneas.py`](../../../../sha3/hax_aeneas.py) and
[`specs/sha3/hax_aeneas.py`](../../../../../specs/sha3/hax_aeneas.py). Internally, these scripts
call `cargo hax into aeneas-lean` and apply small fixes to the output.
The resulting Lean files are:
* [`specs/sha3/proofs/aeneas-lean/HacspecSha3/Extraction/Funs.lean`](../../../../../specs/sha3/proofs/aeneas-lean/HacspecSha3/Extraction/Funs.lean)
* [`libcrux-iot/sha3/proofs/aeneas-lean/LibcruxIotSha3/Extraction/Funs.lean`](Extraction/Funs.lean)

## Reproduction

### Prerequisites

- For running the proofs:
  - Lean 4 toolchain `leanprover/lean4:v4.28.0-rc1` (pinned in `lean-toolchain`).
- For extraction:
  - Hax at commit `7b4bd97058e0fcbf9135b76297ca91942f2327a6`
    (not publicly available yet, https://github.com/cryspen/hax-evit)
  - Charon at commit `ed22146b1cd4d0b578006a58b3299d41ecbe0fd4`
  - Aeneas at commit `b5c45e84` (from https://github.com/cryspen/aeneas)

### Building

From `libcrux-iot/sha3/proofs/aeneas-lean/`:

```bash
lake exe cache get        # downloading the Mathlib cache
lake build                # building the project
```

### Cross-spec regression (Rust)

We have a couple of Rust tests in place as a first sanity check that
implementation and specification agree:

```bash
cargo test --lib cross_spec --tests
```

This catches lane-layout / round-constant / endianness mismatches at
the Rust level, before they propagate into Lean proof failures.

### Extraction from Rust into Lean

```bash
# Spec side:
cd specs/sha3/
/hax_aeneas.py

# Impl side:
cd libcrux-iot/sha3/
./hax_aeneas.py
```

