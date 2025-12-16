#!/bin/sh

repo_root=$(git rev-parse --show-toplevel)

$repo_root/c/c.sh --extract ml-dsa --config $repo_root/c/mldsa.yml --no-glue --dep sha3 --libcrux-dep secrets --clean cfiles
