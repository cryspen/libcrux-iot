# SHA3 Crate — Claude Context

## Overview

This crate implements SHA-3 (FIPS 202) targeting IoT/embedded environments (no_std, 32-bit).
The implementation uses a bit-interleaved 2×u32 lane representation (`Lane2U32`) instead of
u64, making it efficient on 32-bit microcontrollers.

It is being set up for formal verification via [hax](https://github.com/cryspen/hax) → F*.

## Module structure

- [src/lane.rs](src/lane.rs) — `Lane2U32`: the 2×u32 bit-interleaved lane type with
  `interleave`/`deinterleave` and bitwise ops
- [src/state.rs](src/state.rs) — `KeccakState`: 5×5 array of `Lane2U32` lanes plus `c`/`d`
  temp arrays; block load/store helpers
- [src/keccak.rs](src/keccak.rs) — `KeccakXofState<RATE>`: absorb/squeeze sponge, plus
  the full Keccak-f\[1600\] permutation (round constants, theta/rho/pi/chi/iota)
- [src/lib.rs](src/lib.rs) — public SHA3/SHAKE API

## Verification setup

- Tool: **hax** extracts Rust → F*; F* typechecks the result
- Config: [proofs/fstar/extraction/hax.fst.config.json](proofs/fstar/extraction/hax.fst.config.json)
- Script: [hax.py](hax.py) — `extract`, `prove`, `clean` sub-commands
- Makefile: [proofs/fstar/extraction/Makefile](proofs/fstar/extraction/Makefile)

### Workflow

```
# Re-extract F* from Rust
./hax.py extract

# Type-check with F*
./hax.py prove

# Lax-check (admit all SMT queries)
./hax.py prove --admit

# Delete generated .fst files
./hax.py clean
```

The extraction feature flag is `unbuffered-xof` (see `hax.py extractAction`).

### F* files

- `Libcrux_iot_sha3.Lane.fst` — lane type and operations
- `Libcrux_iot_sha3.State.fst` — KeccakState
- `Libcrux_iot_sha3.Keccak.fst` — KeccakXofState and permutation
- `proofs/fstar/secrets/` — libcrux-secrets integer types (U32, U8) for F*

## Work done on `franziskus/sha3-runtime-safety`

This branch was created from `jonas/sha3-runtime-safety` at commit `d765fb0`.

### What Jonas did (on `jonas/sha3-runtime-safety`)

| Commit | Description |
|--------|-------------|
| `f427d87` | Basic hax extraction setup (hax.py, Makefile, config) |
| `524187f` | Runtime safety annotations (`#[hax_lib::requires]`) for `lane` module |
| `495df3d` | Initial F* extraction — generated Lane, State, partial Keccak .fst files |
| `a3c49b3` | Runtime safety annotations for `state` module |
| `1b1cae6` | Updated extraction |
| `4fa94aa` | Fixed `hax.py clean` when glob returns no files |
| `4848511` | WIP: extended extraction to `keccak` module (absorb/squeeze annotated) |
| `2c7bd9f` | WIP: keccak module sans permutation (RC constants still opaque) |
| `d765fb0` | WIP: almost full extraction, most functions extracted; RC constants and some permutation steps still assumed (`assume val`) because `#[hax_lib::fstar::options]` can't be used inside `impl` blocks (hax issue [#1698](https://github.com/cryspen/hax/issues/1698)) |

### What Franziskus did (commit `037ea19`)

**`src/keccak.rs`**
- Extracted the body of `KeccakXofState::squeeze` into a top-level `_squeeze` free function.
  This was the workaround for hax issue [#1698](https://github.com/cryspen/hax/issues/1698):
  `#[hax_lib::fstar::options]` cannot be placed on methods inside `impl` blocks, but the
  `squeeze` function needs `--z3rlimit 60` to verify. The method now just delegates to `_squeeze`.
- Removed (commented out) `#[hax_lib::opaque]` from `RC_INTERLEAVED_0`, `RC_INTERLEAVED_1`,
  and many round-constant helper functions. This allows hax to see through them and extract
  actual F* definitions instead of `assume val` stubs.

**`src/state.rs`**
- Added `#[hax_lib::ensures(|_| future(self).i == self.i)]` to `set_with_zeta`, `set_lane`,
  and `set_lane_value` — these help F* reason that the `i` index parameter doesn't get
  modified through the mutable self borrow.
- Added `#[hax_lib::ensures(|_| future(out).len() == out.len())]` to `store_block` and
  `store_block_full` to preserve length invariants across the output slice.

**`proofs/fstar/extraction/Libcrux_iot_sha3.Keccak.fst`**
- Replaced hundreds of `assume val` stubs with concrete F* definitions for:
  - `RC_INTERLEAVED_0` and `RC_INTERLEAVED_1` arrays (255 u32 elements each)
  - All `keccakf1600_round*` functions (theta/rho/pi/chi/iota steps for each round)
- The file grew from ~600 lines to ~6100 lines.

**`proofs/fstar/extraction/Libcrux_iot_sha3.State.fst`**
- Added `let open Libcrux_iot_sha3.Lane in` to the implicit-dependencies block.
- Added ensures postconditions to several state mutation functions.

## Known hax issues and workarounds

| Issue | Workaround |
|-------|-----------|
| `#[hax_lib::fstar::options]` not allowed on `impl` methods ([#1698](https://github.com/cryspen/hax/issues/1698)) | Extract method body to a free `fn` and annotate there; method delegates to it |
| `IndexMut` for `Lane2U32` breaks hax | Directly index `self.c[i].0[j] = value` instead |
| Eurydice doesn't extract `core::cmp::min` ([eurydice #49](https://github.com/AeneasVerif/eurydice/issues/49)) | Use explicit `if RATE >= out_len { out_len } else { RATE }` |
| `hax.py clean` fails on empty glob | Fixed in `4fa94aa` by checking if glob returns files before calling `rm` |
| `store_block_full` requires slice coercion | Use `&mut out[..]` under `#[cfg(hax)]` (hax issue [#1983](https://github.com/cryspen/hax/issues/1983)) |

## What still needs work

- Some parts of the permutation may still be assumed in F* (check for remaining `assume val` in `Libcrux_iot_sha3.Keccak.fst`)
- The `#[hax_lib::fstar::options]` workaround for `squeeze` uses `out: &mut [u8]` (unclassified) instead of `&mut [U8]` — may need fixing for secret-independence
- F* typecheck (`./hax.py prove`) has not been confirmed to pass end-to-end yet on this branch
