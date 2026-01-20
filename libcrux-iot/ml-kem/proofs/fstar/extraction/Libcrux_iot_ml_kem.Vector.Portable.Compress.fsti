module Libcrux_iot_ml_kem.Vector.Portable.Compress
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_secrets.Int in
  let open Libcrux_secrets.Int.Public_integers in
  let open Libcrux_secrets.Traits in
  ()

/// The `compress_*` functions implement the `Compress` function specified in the NIST FIPS
/// 203 standard (Page 18, Expression 4.5), which is defined as:
/// ```plaintext
/// Compress_d: ℤq -> ℤ_{2ᵈ}
/// Compress_d(x) = ⌈(2ᵈ/q)·x⌋
/// ```
/// Since `⌈x⌋ = ⌊x + 1/2⌋` we have:
/// ```plaintext
/// Compress_d(x) = ⌊(2ᵈ/q)·x + 1/2⌋
///               = ⌊(2^{d+1}·x + q) / 2q⌋
/// ```
/// For further information about the function implementations, consult the
/// `implementation_notes.pdf` document in this directory.
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
val compress_message_coefficient (fe: u16) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val compress_ciphertext_coefficient (coefficient_bits: u8) (fe: u16)
    : Prims.Pure i16 (requires coefficient_bits <=. mk_u8 16) (fun _ -> Prims.l_True)

val compress_1_ (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val compress
      (v_COEFFICIENT_BITS: i32)
      (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires v_COEFFICIENT_BITS >=. mk_i32 0 && v_COEFFICIENT_BITS <=. mk_i32 16)
      (fun _ -> Prims.l_True)

val decompress_ciphertext_coefficient
      (v_COEFFICIENT_BITS: i32)
      (a: Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure Libcrux_iot_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires mk_i32 0 <=. v_COEFFICIENT_BITS && v_COEFFICIENT_BITS <. mk_i32 31)
      (fun _ -> Prims.l_True)
