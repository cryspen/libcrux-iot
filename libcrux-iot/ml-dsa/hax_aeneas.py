#!/usr/bin/env python3
"""Extraction driver for libcrux-iot ML-DSA NTT → Lean.

Mirrors `libcrux-iot/ml-kem/hax_aeneas.py`. Three responsibilities:

1. Pin/check the hax + aeneas toolchain versions.
2. Run `cargo hax into aeneas-lean` with a Charon `--start-from` list chosen
   to bound the extraction to the NTT / arithmetic / matrix core.
3. Patch the generated `LibcruxIotMlDsa/Extraction/Funs.lean` in-place.

TOOLCHAIN NOTE (Phase-0 gate): the versions below match the Hax *Lean library*
pinned in `proofs/aeneas-lean/lakefile.toml` (hax-evit `ffdf432...`). The
aeneas *binary* that produces output compatible with that library is
`8d2077c`. If `cargo hax`/`aeneas` on PATH report different revs (e.g. the
SHA-3-era `b5c45e84` aeneas), extraction may produce a `Funs.lean` that does
not type-check against the pinned Hax library. Build the matching aeneas from
source (see ml-kem `README.md` §Reproduction) before relying on this driver,
or use `SKIP_VERSION_CHECK=1` to experiment (real escape hatch — downstream
build may fail).

The ML-DSA impl carries NO `#[hax_lib::*]` annotations and uses const generics
(`outer_3_plus<OFFSET, STEP_BY, ZETA>`, `shift_left_then_reduce<SHIFT_BY>`).
Extraction does not *require* annotations, but confirm aeneas monomorphizes the
const-generic layer steps into usable `Funs.lean` defs (ML-KEM's parametric
`ntt_at_layer_4_plus` is the precedent that this works).
"""

import os
import re
import subprocess
import sys
from pathlib import Path

HAX_VERSION = "ffdf432705d409b62ec025d253a340234b59766f"
AENEAS_VERSION = "8d2077c"

# Charon translation roots. Anything not reachable from these is dropped from
# `Funs.lean`. The NTT/arithmetic core lives in the portable SIMD module; the
# matrix pipelines drive iNTT.
START_FROM = [
    "crate::ntt::*",
    "crate::polynomial::*",
    "crate::arithmetic::*",
    "crate::simd::portable::ntt::*",
    "crate::simd::portable::invntt::*",
    "crate::simd::portable::arithmetic::*",
    "crate::simd::portable::vector_type::*",
    # Verification-only anchor (ntt.rs, `#[cfg(hax_backend_lean)]`) that instantiates the
    # generic polynomial/ntt API at the concrete `Coefficients` SIMD unit. This
    # is the reachable, non-opaque, monomorphic *user* of the
    # `Operations for Coefficients` trait impl that Charon needs to retain the
    # instance (ML-DSA's real users — matrix / ml_dsa_generic — are opaque, so
    # without it the impl is pruned). Mirrors ML-KEM's non-opaque matrix roots.
    "crate::ntt::_portable_operations_anchor",
    "crate::simd::traits::*",
    "crate::matrix::compute_as1_plus_s2",
    "crate::matrix::compute_matrix_x_mask",
]

# Items to keep opaque (extract signature only). The hash/sampling/encoding
# glue is out of scope for the NTT campaign; SHA-3 is verified in
# libcrux-iot/sha3.
OPAQUE = [
    "crate::hash_functions::*",
    "crate::sample::*",
    "crate::samplex4::*",
    "crate::encoding::*",
    "crate::ml_dsa_generic::*",
    "crate::pre_hash::*",
    # The impl's serialize/sample methods forward to these nested portable
    # modules, whose bodies use unmodeled chunks_exact/as_u8. They are out of
    # the NTT/arithmetic scope, so keep them opaque (signature only); the
    # Operations instance's serialize/sample fields then forward to opaque
    # leaves, while the NTT/arith fields forward to the verified concrete fns.
    "crate::simd::portable::encoding::*",
    "crate::simd::portable::sample::*",
    # Phase-7 vector drivers that iterate a `&mut [PolynomialRingElement]` with a
    # nested slice iterator (hax issue #720). The installed aeneas cannot
    # translate that region pattern and emits a `sorry` body; keep them opaque
    # (signature only) so the extraction stays axiom-/sorry-free. The NTT core
    # (Phases 2–6) does not use them; the per-element `power2round_element` /
    # `decompose_element` (the actual Phase-7 FC targets) extract fine.
    "crate::arithmetic::power2round_vector",
    "crate::arithmetic::decompose_vector",
    # Phase-8 (matrix-level) drivers: the pinned aeneas renders their nested
    # loops with a malformed `matrix.compute_*_loop0` field-projection on the
    # bounded-`Vec` subtype (`{ l // l.length ≤ Usize.max }`). Phase 8 is the
    # last/optional phase (and may instead compose from `Spec/Pure` per
    # `Plan.lean`), so keep them opaque to get a clean NTT-core (Phases 2–7)
    # build; revisit the matrix extraction when Phase 8 starts.
    "crate::matrix::compute_as1_plus_s2",
    "crate::matrix::compute_matrix_x_mask",
]


def check_version(cmd: list[str], expected: str) -> None:
    result = subprocess.run(cmd, capture_output=True, text=True)
    output = result.stdout + result.stderr
    if expected not in output:
        if os.environ.get("SKIP_VERSION_CHECK") == "1":
            print(f"warning: version mismatch for {cmd[0]} (expected {expected!r}); "
                  f"continuing because SKIP_VERSION_CHECK=1", file=sys.stderr)
            return
        print(f"Version mismatch for {cmd[0]}: expected {expected!r} in output:\n{output}",
              file=sys.stderr)
        sys.exit(1)


check_version(["cargo", "hax", "--version"], HAX_VERSION)
check_version(["aeneas", "-version"], AENEAS_VERSION)

charon_args = " ".join(
    [f"--start-from {root}" for root in START_FROM] +
    [f"--opaque {item}" for item in OPAQUE]
)

result = subprocess.run(
    ["cargo", "hax", "into", "aeneas-lean",
     "--aeneas-args=-core-models-lib",
     f"--charon-args={charon_args}"],
    env={**os.environ, "RUSTFLAGS": "--cfg hax_backend_lean"},
)
if result.returncode != 0:
    sys.exit(result.returncode)

funs_lean = Path("proofs/aeneas-lean/LibcruxIotMlDsa/Extraction/Funs.lean")
content = funs_lean.read_text()

# Import the hand-written `Missing.lean` (libcrux_secrets I32 classify/declassify
# stubs etc.), mirroring the ml-kem patch.
content = content.replace(
    "import CoreModels",
    "import CoreModels\n"
    "import LibcruxIotMlDsa.Extraction.Missing",
    1,
)

# Convert `axiom` declarations emitted for `--opaque` items to `opaque`
# (`axiom` shows up in `#print axioms`; `opaque` does not).
content = re.sub(r"^axiom ", "opaque ", content, flags=re.MULTILINE)

# TODO(Phase 0): add ML-DSA-specific call-site patches here if aeneas drops
# trait-instance arguments (the ml-kem driver patches `vectortraitsOperationsInst`
# / `hash_functionsHashInst` insertions). Re-derive empirically from the first
# extraction's build errors — do NOT copy the ml-kem patch list blind.

funs_lean.write_text(content)
print("Patched", funs_lean)
