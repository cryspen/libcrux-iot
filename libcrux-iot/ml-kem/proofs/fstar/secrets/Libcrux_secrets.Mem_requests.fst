module Libcrux_secrets.Mem_requests
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// Mark memory as secret.
/// No-op if `valgrind_ct_test` cfg is not enabled.
let ct_classify (#v_T: Type0) (v_val: v_T) : Prims.unit = ()

/// Declassify secret memory.
/// No-op if `valgrind_ct_test` cfg is not enabled.
let ct_declassify (#v_T: Type0) (v_val: v_T) : Prims.unit = ()
