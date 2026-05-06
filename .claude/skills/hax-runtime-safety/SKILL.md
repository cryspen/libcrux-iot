---
name: hax-runtime-safety
description: Adds hax runtime safety annotations to Rust code
disable-model-invocations: true
arguments: module crate
---

## Your Task

Add runtime safety annotations to module $module of $crate.

1. Make sure you are in the working directory of crate $crate.
2. For all functions in $module that are not marked with `#[hax_lib::opaque]` add or update runtime safety annotations according to `examples.md`.

## Guidelines for Runtime Safety Annotations

- Use Rust annotations only, avoid the `fstar!` macro and raw F* code in the `requires`, `ensures` and `loop_invariant!` macros.
- Propagate runtime safety pre-conditions to callers, if necessary.
- Example annotations are given in `examples.md`.
