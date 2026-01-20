module Libcrux_iot_ml_kem.Constants
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

/// Coefficients per ring element
let v_COEFFICIENTS_IN_RING_ELEMENT: usize = mk_usize 256

/// Bits required per (uncompressed) ring element
let v_BITS_PER_RING_ELEMENT: usize = v_COEFFICIENTS_IN_RING_ELEMENT *! mk_usize 12

/// Bytes required per (uncompressed) ring element
let v_BYTES_PER_RING_ELEMENT: usize = v_BITS_PER_RING_ELEMENT /! mk_usize 8

/// The size of an ML-KEM shared secret.
let v_SHARED_SECRET_SIZE: usize = mk_usize 32
