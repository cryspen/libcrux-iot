#!/usr/bin/env python3

import os
import re
import subprocess
import sys
from pathlib import Path

HAX_VERSION = "1f85fc13b9967080cc657863e2000ba5d4aa8647"
AENEAS_VERSION = "8d2077c"


def check_version(cmd: list[str], name: str, expected: str) -> None:
    result = subprocess.run(cmd, capture_output=True, text=True)
    output = result.stdout + result.stderr
    if expected not in output:
        print(f"Version mismatch for {name}: expected {expected!r} in output:\n{output}", file=sys.stderr)
        sys.exit(1)


check_version(["cargo", "hax", "--version"], "hax", HAX_VERSION)
check_version(["aeneas", "-version"], "aeneas", AENEAS_VERSION)

result = subprocess.run(
    ["cargo", "hax", "into", "aeneas-lean", '--aeneas-args="-core-models-lib"'],
    env={**os.environ, "RUSTFLAGS": "--cfg hax_backend_lean"},
)

# Aeneas reports a non-zero exit when it can't generate a definition for an
# extracted external item (here: the `Debug` derive on `Algorithm`). The
# generated Funs.lean still has the axiom inline, so we tolerate this
# specific failure and continue with the post-processing below.
if result.returncode != 0:
    print(f"warning: aeneas exited with code {result.returncode}; "
          f"continuing with post-processing (axiom remains inline).",
          file=sys.stderr)

funs_lean = Path("proofs/aeneas-lean/LibcruxIotSha3/Extraction/Funs.lean")
content = funs_lean.read_text()

content = re.sub(
    r"(^import Aeneas\b)",
    r"\1\nimport LibcruxIotSha3.Extraction.Missing",
    content,
    count=1,
    flags=re.MULTILINE,
)

# Wrong signature of `core_models.fmt.rt.Argument.new_display`
panic_block = (
    "    let a ←\n"
    "      core.fmt.rt.Argument.new_display core.Usize.Insts.CoreFmtDisplay i\n"
    "    let a1 ←\n"
    "      core.fmt.rt.Argument.new_display core.Usize.Insts.CoreFmtDisplay RATE\n"
    "    let _ ←\n"
    "      core.fmt.Arguments.new\n"
    "        (Array.make 7#usize [\n"
    "          192#u8, 3#u8, 32#u8, 62#u8, 32#u8, 192#u8, 0#u8\n"
    "          ]) (Array.make 2#usize [ a, a1 ])\n"
    "    fail panic"
)
content = content.replace(panic_block, "/-\n" + panic_block + "\n-/\n    fail panic", 1)

funs_lean.write_text(content)
