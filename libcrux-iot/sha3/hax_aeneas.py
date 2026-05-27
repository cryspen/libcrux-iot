#!/usr/bin/env python3

import os
import re
import subprocess
import sys
from pathlib import Path

HAX_VERSION = "7b4bd97058e0fcbf9135b76297ca91942f2327a6"
AENEAS_VERSION = "b5c45e84"


def check_version(cmd: list[str], name: str, expected: str) -> None:
    result = subprocess.run(cmd, capture_output=True, text=True)
    output = result.stdout + result.stderr
    if expected not in output:
        print(f"Version mismatch for {name}: expected {expected!r} in output:\n{output}", file=sys.stderr)
        sys.exit(1)


check_version(["cargo", "hax", "--version"], "hax", HAX_VERSION)
check_version(["aeneas", "-version"], "aeneas", AENEAS_VERSION)

result = subprocess.run(
    ["cargo", "hax", "into", "aeneas-lean"],
    env={**os.environ, "RUSTFLAGS": "--cfg charon"},
    capture_output=True,
    text=True,
)

# Suppress version mismatch warnings. (We check versions above.)
_ANSI = re.compile(r'\x1b\[[0-9;]*[a-zA-Z]')
def should_suppress(line: str) -> bool:
    plain = _ANSI.sub('', line)
    return plain.startswith("warning: hax: aeneas version mismatch:") or plain.startswith("warning: hax: charon version mismatch:")

for line in result.stdout.splitlines():
    if not should_suppress(line):
        print(line)
for line in result.stderr.splitlines():
    if not should_suppress(line):
        print(line, file=sys.stderr)
if result.returncode != 0:
    sys.exit(result.returncode)

funs_lean = "proofs/aeneas-lean/LibcruxIotSha3/Extraction/Funs.lean"
with open(funs_lean) as f:
    content = f.read()

content = content.replace(
    "import Aeneas",
    "import Aeneas\nimport LibcruxIotSha3.Extraction.Missing\nopen core_models",
    1,
)

# This definition is hitting the recursion limit:
content = content.replace(
    "/-- [libcrux_iot_sha3::keccak::RC_INTERLEAVED_1]",
    "set_option maxRecDepth 1000 in\n/-- [libcrux_iot_sha3::keccak::RC_INTERLEAVED_1]",
    1,
)

# This definition is hitting the recursion limit:
content = content.replace(
    "/-- [libcrux_iot_sha3::keccak::RC_INTERLEAVED_0]",
    "set_option maxRecDepth 1000 in\n/-- [libcrux_iot_sha3::keccak::RC_INTERLEAVED_0]",
    1,
)

# Wrong signature of `core_models.fmt.rt.Argument.new_display`
block = (
    "    let a ←\n"
    "      core_models.fmt.rt.Argument.new_display\n"
    "        core_models.Usize.Insts.Core_modelsFmtDisplay i\n"
    "    let a1 ←\n"
    "      core_models.fmt.rt.Argument.new_display\n"
    "        core_models.Usize.Insts.Core_modelsFmtDisplay RATE\n"
    "    let _ ←\n"
    "      core_models.fmt.Arguments.new\n"
    "        (Array.make 7#usize [\n"
    "          192#u8, 3#u8, 32#u8, 62#u8, 32#u8, 192#u8, 0#u8\n"
    "          ]) (Array.make 2#usize [ a, a1 ])"
)
content = content.replace(block, "/-\n" + block + "\n-/", 1)

# Wrong field name in `core_models.fmt.Debug`
content = content.replace(
    "  fmt := ",
    "  dbg_fmt := ",
    1,
)


with open(funs_lean, "w") as f:
    f.write(content)
