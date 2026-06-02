#!/bin/sh

repo_root=$(git rev-parse --show-toplevel)

$repo_root/c/c.sh --extract ml-kem --config $repo_root/c/mlkem.yml --dep sha3 --libcrux-dep secrets --clean cfiles
