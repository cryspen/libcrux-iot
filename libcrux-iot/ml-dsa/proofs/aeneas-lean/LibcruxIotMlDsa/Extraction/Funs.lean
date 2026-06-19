/-!
# `Extraction/Funs.lean` — GENERATED, do not hand-edit

This file is produced by `libcrux-iot/ml-dsa/hax_aeneas.py`
(`cargo hax into aeneas-lean` + in-place patches). It is **not yet generated**
in this scaffold because the locally-installed hax/aeneas binaries do not match
the pins in `hax_aeneas.py` (`HAX_VERSION = ffdf432…`, `AENEAS_VERSION = 8d2077c`).

## Phase 0 — to generate this file

1. Install/build the matching toolchain (see `ml-kem/proofs/aeneas-lean/`
   `README.md` §Reproduction — build aeneas from source at `8d2077c`).
2. From `libcrux-iot/ml-dsa/`, run `./hax_aeneas.py`.
3. The generated file replaces this placeholder; it will contain
   `ntt.*`, `simd.portable.{ntt,invntt,arithmetic,vector_type}.*`,
   `polynomial.*`, `arithmetic.*`, and the matrix composers under namespace
   `libcrux_iot_ml_dsa.*`.
4. Fill `Extraction/Missing.lean` with whatever `libcrux_secrets` i32 cast
   stubs the generated file references (derive from the first build's errors).
5. Then `LibcruxIotMlDsa.lean` (the root) re-enables the `Extraction.Funs`,
   `Util`, and `Plan` imports, and Phase 1+ proofs begin.

Until then this placeholder is intentionally empty so the self-contained
`Spec/` reference builds without a real extraction.
-/
