#!/bin/sh

repo_root=$(git rev-parse --show-toplevel)

$repo_root/c/c.sh --extract sha3 --config $repo_root/c/sha3.yml --no-glue --libcrux-dep secrets --clean cfiles
