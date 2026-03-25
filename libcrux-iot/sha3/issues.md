- charon cannot handle `impl core::fmt::Debug for Lane2U32` in `lane.rs`, which seems to be a known issue.

- The namespaced expression `state.KeccakState` clashes with a variable called `state`. Lean misunderstands the namespace notation
as dot-notation. (`libcrux_iot_sha3::state::load_block_2u32`)

- Need to set `set_option maxRecDepth 1000 in` for `RC_INTERLEAVED_1`

- keccak functions are too large. I split them like for Hax. What is going on with the `full-unroll`?
  It sets `let i = s.i` only in some configs?