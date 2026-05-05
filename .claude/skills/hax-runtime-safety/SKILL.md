---
name: hax-runtime-safety
description: Adds hax runtime safety annotations to Rust code
disable-model-invocations: true
arguments: module crate
---

## Your Task

Add runtime safety annotations to module $module of $crate.

1. Change working directory to that of crate $crate.
2. Clean up previous F* extraction with `./hax.py clean`.
3. If necessary, extend the list of extracted modules in `hax.py` to include $module.
4. Extract the crate to F* with `./hax.py extract`.
5. Run `./hax.py prove` in the directory of $crate.
6. If `hax.py prove` passes without errors you are done.
7. Else, if `hax.py prove` results in errors, add the missing runtime safety annotations to $module and the modules it depends on, if necessary.
8. Repeat from step 1 until `hax.py prove` passes without errors.

## Guidelines for Runtime Safety Annotations

- Use Rust annotations only, avoid the `fstar!` macro and raw F* code in the `requires`, `ensures` and `loop_invariant!` macros.
- Propagate runtime safety pre-conditions to callers, if necessary.
