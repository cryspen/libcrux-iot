module Libcrux_iot_ml_kem.Vector.Portable.Vector_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

type t_PortableVector = { f_elements:t_Array i16 (mk_usize 16) }

let impl: Core.Clone.t_Clone t_PortableVector =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }
