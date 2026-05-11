module Libcrux_iot_sha3.Keccak
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_iot_sha3.Lane in
  let open Libcrux_secrets.Int.Public_integers in
  let open Libcrux_secrets.Traits in
  ()

/// The internal keccak state that can also buffer inputs to absorb.
/// This is used in the general xof APIs.
type t_KeccakXofState (v_RATE: usize) = {
  f_inner:Libcrux_iot_sha3.State.t_KeccakState;
  f_buf:t_Array u8 v_RATE;
  f_buf_len:usize;
  f_sponge:bool
}

/// An all zero block
let impl__zero_block (v_RATE: usize) (_: Prims.unit) : t_Array u8 v_RATE =
  Libcrux_secrets.Traits.f_classify #(t_Array u8 v_RATE)
    #FStar.Tactics.Typeclasses.solve
    (Rust_primitives.Hax.repeat (mk_u8 0) v_RATE <: t_Array u8 v_RATE)

/// Generate a new keccak xof state.
let impl__new (v_RATE: usize) (_: Prims.unit) : t_KeccakXofState v_RATE =
  {
    f_inner = Libcrux_iot_sha3.State.impl_KeccakState__new ();
    f_buf = impl__zero_block v_RATE ();
    f_buf_len = mk_usize 0;
    f_sponge = false
  }
  <:
  t_KeccakXofState v_RATE

/// Consume the internal buffer and the required amount of the input to pad to
/// `RATE`.
/// Returns the `consumed` bytes from `inputs` if there\'s enough buffered
/// content to consume, and `0` otherwise.
/// If `consumed > 0` is returned, `self.buf` contains a full block to be
/// loaded.
let impl__fill_buffer (v_RATE: usize) (self: t_KeccakXofState v_RATE) (inputs: t_Slice u8)
    : Prims.Pure (t_KeccakXofState v_RATE & usize)
      (requires
        self.f_buf_len <=. v_RATE &&
        ((Rust_primitives.Hax.Int.from_machine (Core_models.Slice.impl__len #u8 inputs <: usize)
            <:
            Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine self.f_buf_len <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_usize__MAX <: Hax_lib.Int.t_Int))
      (ensures
        fun temp_0_ ->
          let (self_e_future: t_KeccakXofState v_RATE), (res: usize) = temp_0_ in
          b2t (res <=. v_RATE <: bool) /\ b2t (self_e_future.f_buf_len <=. v_RATE <: bool) /\
          (b2t (res >. mk_usize 0 <: bool) ==> b2t (self_e_future.f_buf_len =. v_RATE <: bool))) =
  let input_len:usize = Core_models.Slice.impl__len #u8 inputs in
  let consumed:usize = mk_usize 0 in
  let (consumed: usize), (self: t_KeccakXofState v_RATE) =
    if self.f_buf_len >. mk_usize 0
    then
      if (self.f_buf_len +! input_len <: usize) >=. v_RATE
      then
        let consumed:usize = v_RATE -! self.f_buf_len in
        let self:t_KeccakXofState v_RATE =
          {
            self with
            f_buf
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from self.f_buf
              ({ Core_models.Ops.Range.f_start = self.f_buf_len }
                <:
                Core_models.Ops.Range.t_RangeFrom usize)
              (Core_models.Slice.impl__copy_from_slice #u8
                  (self.f_buf.[ { Core_models.Ops.Range.f_start = self.f_buf_len }
                      <:
                      Core_models.Ops.Range.t_RangeFrom usize ]
                    <:
                    t_Slice u8)
                  (inputs.[ { Core_models.Ops.Range.f_end = consumed }
                      <:
                      Core_models.Ops.Range.t_RangeTo usize ]
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
          }
          <:
          t_KeccakXofState v_RATE
        in
        let self:t_KeccakXofState v_RATE =
          { self with f_buf_len = self.f_buf_len +! consumed } <: t_KeccakXofState v_RATE
        in
        consumed, self <: (usize & t_KeccakXofState v_RATE)
      else consumed, self <: (usize & t_KeccakXofState v_RATE)
    else consumed, self <: (usize & t_KeccakXofState v_RATE)
  in
  let hax_temp_output:usize = consumed in
  self, hax_temp_output <: (t_KeccakXofState v_RATE & usize)

let v_RC_INTERLEAVED_0_: t_Array u32 (mk_usize 255) =
  let list =
    [
      mk_u32 1; mk_u32 0; mk_u32 0; mk_u32 0; mk_u32 1; mk_u32 1; mk_u32 1; mk_u32 1; mk_u32 0;
      mk_u32 0; mk_u32 1; mk_u32 0; mk_u32 1; mk_u32 1; mk_u32 1; mk_u32 1; mk_u32 0; mk_u32 0;
      mk_u32 0; mk_u32 0; mk_u32 1; mk_u32 0; mk_u32 1; mk_u32 0; mk_u32 0; mk_u32 0; mk_u32 1;
      mk_u32 1; mk_u32 0; mk_u32 1; mk_u32 0; mk_u32 1; mk_u32 1; mk_u32 1; mk_u32 1; mk_u32 1;
      mk_u32 0; mk_u32 0; mk_u32 1; mk_u32 1; mk_u32 1; mk_u32 1; mk_u32 0; mk_u32 1; mk_u32 1;
      mk_u32 0; mk_u32 0; mk_u32 1; mk_u32 0; mk_u32 1; mk_u32 0; mk_u32 1; mk_u32 1; mk_u32 1;
      mk_u32 0; mk_u32 1; mk_u32 0; mk_u32 1; mk_u32 1; mk_u32 0; mk_u32 1; mk_u32 1; mk_u32 1;
      mk_u32 0; mk_u32 0; mk_u32 1; mk_u32 1; mk_u32 0; mk_u32 1; mk_u32 0; mk_u32 0; mk_u32 1;
      mk_u32 1; mk_u32 0; mk_u32 1; mk_u32 1; mk_u32 0; mk_u32 1; mk_u32 0; mk_u32 0; mk_u32 0;
      mk_u32 1; mk_u32 0; mk_u32 0; mk_u32 1; mk_u32 1; mk_u32 1; mk_u32 0; mk_u32 1; mk_u32 1;
      mk_u32 0; mk_u32 1; mk_u32 1; mk_u32 0; mk_u32 0; mk_u32 0; mk_u32 0; mk_u32 1; mk_u32 1;
      mk_u32 1; mk_u32 0; mk_u32 1; mk_u32 0; mk_u32 0; mk_u32 1; mk_u32 0; mk_u32 0; mk_u32 1;
      mk_u32 0; mk_u32 0; mk_u32 0; mk_u32 0; mk_u32 0; mk_u32 1; mk_u32 0; mk_u32 1; mk_u32 1;
      mk_u32 0; mk_u32 0; mk_u32 0; mk_u32 1; mk_u32 1; mk_u32 1; mk_u32 0; mk_u32 0; mk_u32 0;
      mk_u32 0; mk_u32 0; mk_u32 0; mk_u32 1; mk_u32 1; mk_u32 0; mk_u32 1; mk_u32 1; mk_u32 1;
      mk_u32 1; mk_u32 0; mk_u32 1; mk_u32 0; mk_u32 0; mk_u32 0; mk_u32 0; mk_u32 0; mk_u32 0;
      mk_u32 0; mk_u32 1; mk_u32 0; mk_u32 0; mk_u32 1; mk_u32 0; mk_u32 1; mk_u32 0; mk_u32 0;
      mk_u32 1; mk_u32 1; mk_u32 1; mk_u32 1; mk_u32 1; mk_u32 1; mk_u32 1; mk_u32 1; mk_u32 0;
      mk_u32 0; mk_u32 0; mk_u32 1; mk_u32 1; mk_u32 0; mk_u32 0; mk_u32 0; mk_u32 1; mk_u32 0;
      mk_u32 1; mk_u32 0; mk_u32 1; mk_u32 0; mk_u32 1; mk_u32 0; mk_u32 0; mk_u32 0; mk_u32 0;
      mk_u32 1; mk_u32 0; mk_u32 0; mk_u32 0; mk_u32 0; mk_u32 1; mk_u32 1; mk_u32 0; mk_u32 0;
      mk_u32 1; mk_u32 1; mk_u32 0; mk_u32 0; mk_u32 0; mk_u32 0; mk_u32 0; mk_u32 1; mk_u32 1;
      mk_u32 1; mk_u32 1; mk_u32 1; mk_u32 0; mk_u32 1; mk_u32 1; mk_u32 1; mk_u32 0; mk_u32 1;
      mk_u32 1; mk_u32 1; mk_u32 1; mk_u32 1; mk_u32 1; mk_u32 0; mk_u32 1; mk_u32 0; mk_u32 1;
      mk_u32 0; mk_u32 0; mk_u32 1; mk_u32 0; mk_u32 1; mk_u32 1; mk_u32 0; mk_u32 1; mk_u32 0;
      mk_u32 1; mk_u32 0; mk_u32 1; mk_u32 1; mk_u32 0; mk_u32 0; mk_u32 1; mk_u32 1; mk_u32 1;
      mk_u32 0; mk_u32 0; mk_u32 1; mk_u32 0; mk_u32 0; mk_u32 1; mk_u32 1; mk_u32 0; mk_u32 0;
      mk_u32 1; mk_u32 0; mk_u32 0; mk_u32 0; mk_u32 1; mk_u32 0; mk_u32 1; mk_u32 1; mk_u32 1;
      mk_u32 0; mk_u32 0; mk_u32 0
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 255);
  Rust_primitives.Hax.array_of_list 255 list

let v_RC_INTERLEAVED_1_: t_Array u32 (mk_usize 255) =
  let list =
    [
      mk_u32 0; mk_u32 137; mk_u32 2147483787; mk_u32 2147516544; mk_u32 139; mk_u32 32768;
      mk_u32 2147516552; mk_u32 2147483778; mk_u32 11; mk_u32 10; mk_u32 32898; mk_u32 32771;
      mk_u32 32907; mk_u32 2147483659; mk_u32 2147483786; mk_u32 2147483777; mk_u32 2147483777;
      mk_u32 2147483656; mk_u32 131; mk_u32 2147516419; mk_u32 2147516552; mk_u32 2147483784;
      mk_u32 32768; mk_u32 2147516546; mk_u32 2147516553; mk_u32 2147516547; mk_u32 2147483649;
      mk_u32 2147516418; mk_u32 2147483785; mk_u32 130; mk_u32 2147483656; mk_u32 137;
      mk_u32 2147483656; mk_u32 0; mk_u32 131; mk_u32 2147516544; mk_u32 8; mk_u32 2147483776;
      mk_u32 2147516544; mk_u32 2; mk_u32 2147516555; mk_u32 8; mk_u32 2147483657; mk_u32 32779;
      mk_u32 2147516546; mk_u32 2147516416; mk_u32 32776; mk_u32 32897; mk_u32 2147516553;
      mk_u32 2147516553; mk_u32 2147516426; mk_u32 138; mk_u32 130; mk_u32 2147483650; mk_u32 32898;
      mk_u32 32896; mk_u32 2147483659; mk_u32 2147483651; mk_u32 10; mk_u32 32769; mk_u32 2147483779;
      mk_u32 32899; mk_u32 139; mk_u32 32778; mk_u32 2147483779; mk_u32 32778; mk_u32 2147483648;
      mk_u32 2147483786; mk_u32 2147483656; mk_u32 10; mk_u32 32904; mk_u32 8; mk_u32 2147483651;
      mk_u32 0; mk_u32 10; mk_u32 32779; mk_u32 2147516552; mk_u32 2147483659; mk_u32 2147483776;
      mk_u32 2147516554; mk_u32 32777; mk_u32 3; mk_u32 2147483651; mk_u32 137; mk_u32 2147483777;
      mk_u32 2147483787; mk_u32 2147516419; mk_u32 2147516427; mk_u32 32776; mk_u32 32776;
      mk_u32 32770; mk_u32 9; mk_u32 2147516545; mk_u32 32906; mk_u32 2147516426; mk_u32 128;
      mk_u32 32905; mk_u32 32906; mk_u32 2147516553; mk_u32 2147516416; mk_u32 32897;
      mk_u32 2147516426; mk_u32 9; mk_u32 2147516418; mk_u32 2147483658; mk_u32 2147516418;
      mk_u32 2147483648; mk_u32 2147483657; mk_u32 32904; mk_u32 2; mk_u32 2147516424;
      mk_u32 2147516552; mk_u32 2147483649; mk_u32 2147516555; mk_u32 2; mk_u32 2147516418;
      mk_u32 2147483779; mk_u32 32905; mk_u32 32896; mk_u32 2147483778; mk_u32 136;
      mk_u32 2147516554; mk_u32 32906; mk_u32 2147516547; mk_u32 2147483659; mk_u32 2147483657;
      mk_u32 32769; mk_u32 2147483785; mk_u32 136; mk_u32 2147516419; mk_u32 2147516417; mk_u32 3;
      mk_u32 2147483776; mk_u32 2147516425; mk_u32 2147483785; mk_u32 11; mk_u32 131;
      mk_u32 2147516425; mk_u32 2147483779; mk_u32 32768; mk_u32 2147516427; mk_u32 32770; mk_u32 3;
      mk_u32 2147483786; mk_u32 2147483650; mk_u32 32769; mk_u32 2147483648; mk_u32 2147483651;
      mk_u32 131; mk_u32 2147516554; mk_u32 32771; mk_u32 32776; mk_u32 32907; mk_u32 2147483778;
      mk_u32 1; mk_u32 32769; mk_u32 2147483658; mk_u32 2147516424; mk_u32 2147516427; mk_u32 32897;
      mk_u32 2147516547; mk_u32 2147483778; mk_u32 130; mk_u32 2147483777; mk_u32 2147483650;
      mk_u32 32904; mk_u32 139; mk_u32 32899; mk_u32 8; mk_u32 2147483786; mk_u32 2147483787;
      mk_u32 2147516554; mk_u32 32896; mk_u32 2147483784; mk_u32 32899; mk_u32 2; mk_u32 2147516545;
      mk_u32 32771; mk_u32 32897; mk_u32 2147516416; mk_u32 32770; mk_u32 138; mk_u32 1;
      mk_u32 32898; mk_u32 32906; mk_u32 2147516416; mk_u32 32907; mk_u32 2147483649;
      mk_u32 2147516545; mk_u32 32777; mk_u32 138; mk_u32 136; mk_u32 2147516425; mk_u32 2147483658;
      mk_u32 2147516555; mk_u32 139; mk_u32 32905; mk_u32 32771; mk_u32 32770; mk_u32 128;
      mk_u32 32778; mk_u32 2147483658; mk_u32 2147516545; mk_u32 32896; mk_u32 2147483649;
      mk_u32 2147516424; mk_u32 2147516546; mk_u32 2147516426; mk_u32 3; mk_u32 2147483657;
      mk_u32 32898; mk_u32 32777; mk_u32 128; mk_u32 32899; mk_u32 129; mk_u32 1; mk_u32 32779;
      mk_u32 2147516417; mk_u32 128; mk_u32 32768; mk_u32 2147516417; mk_u32 9; mk_u32 2147516555;
      mk_u32 129; mk_u32 130; mk_u32 2147483787; mk_u32 2147516425; mk_u32 2147483648;
      mk_u32 2147483776; mk_u32 2147516419; mk_u32 2147516546; mk_u32 2147516547; mk_u32 2147483784;
      mk_u32 32905; mk_u32 32777; mk_u32 9; mk_u32 2147516424; mk_u32 2147516417; mk_u32 138;
      mk_u32 11; mk_u32 137; mk_u32 2147483650; mk_u32 32779; mk_u32 2147516427; mk_u32 32907;
      mk_u32 2147483784; mk_u32 32778; mk_u32 2147483785; mk_u32 1; mk_u32 32904; mk_u32 129;
      mk_u32 136; mk_u32 2147516544; mk_u32 129; mk_u32 11
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 255);
  Rust_primitives.Hax.array_of_list 255 list

let keccakf1600_round0_theta_c_x0_z0 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 0) (mk_usize 0)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 0) (mk_usize 0)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 0) (mk_usize 0)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 0) (mk_usize 0)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 0) (mk_usize 0)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 0)
      (mk_usize 0)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round0_theta_c_x0_z1 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 0) (mk_usize 1)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 0) (mk_usize 1)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 0) (mk_usize 1)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 0) (mk_usize 1)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 0) (mk_usize 1)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 0)
      (mk_usize 1)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round0_theta_c_x1_z0 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 1) (mk_usize 0)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 1) (mk_usize 0)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 1) (mk_usize 0)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 1) (mk_usize 0)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 1) (mk_usize 0)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 1)
      (mk_usize 0)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round0_theta_c_x1_z1 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 1) (mk_usize 1)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 1) (mk_usize 1)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 1) (mk_usize 1)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 1) (mk_usize 1)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 1) (mk_usize 1)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 1)
      (mk_usize 1)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round0_theta_c_x2_z0 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 2) (mk_usize 0)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 2) (mk_usize 0)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 2) (mk_usize 0)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 2) (mk_usize 0)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 2) (mk_usize 0)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 2)
      (mk_usize 0)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round0_theta_c_x2_z1 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 2) (mk_usize 1)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 2) (mk_usize 1)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 2) (mk_usize 1)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 2) (mk_usize 1)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 2) (mk_usize 1)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 2)
      (mk_usize 1)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round0_theta_c_x3_z0 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 3) (mk_usize 0)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 3) (mk_usize 0)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 3) (mk_usize 0)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 3) (mk_usize 0)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 3) (mk_usize 0)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 3)
      (mk_usize 0)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round0_theta_c_x3_z1 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 3) (mk_usize 1)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 3) (mk_usize 1)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 3) (mk_usize 1)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 3) (mk_usize 1)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 3) (mk_usize 1)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 3)
      (mk_usize 1)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round0_theta_c_x4_z0 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 4) (mk_usize 0)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 4) (mk_usize 0)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 4) (mk_usize 0)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 4) (mk_usize 0)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 4) (mk_usize 0)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 4)
      (mk_usize 0)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round0_theta_c_x4_z1 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 4) (mk_usize 1)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 4) (mk_usize 1)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 4) (mk_usize 1)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 4) (mk_usize 1)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 4) (mk_usize 1)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 4)
      (mk_usize 1)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round0_theta_d_x0 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let c_x4_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 4 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let c_x1_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 1 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x4_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 4 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x1_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 1 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 0)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 0 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 0 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 0)
              (c_x4_zeta0 ^. (Core_models.Num.impl_u32__rotate_left c_x1_zeta1 (mk_u32 1) <: u32)
                <:
                u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 0)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 0 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 0 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 1)
              (c_x4_zeta1 ^. c_x1_zeta0 <: u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  s

let keccakf1600_round0_theta_d_x1 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let c_x0_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 0 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let c_x2_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 2 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x0_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 0 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x2_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 2 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 1)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 1 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 1 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 0)
              (c_x0_zeta0 ^. (Core_models.Num.impl_u32__rotate_left c_x2_zeta1 (mk_u32 1) <: u32)
                <:
                u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 1)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 1 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 1 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 1)
              (c_x0_zeta1 ^. c_x2_zeta0 <: u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  s

let keccakf1600_round0_theta_d_x2 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let c_x1_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 1 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let c_x3_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 3 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x1_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 1 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x3_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 3 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 2)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 2 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 2 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 0)
              (c_x1_zeta0 ^. (Core_models.Num.impl_u32__rotate_left c_x3_zeta1 (mk_u32 1) <: u32)
                <:
                u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 2)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 2 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 2 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 1)
              (c_x1_zeta1 ^. c_x3_zeta0 <: u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  s

let keccakf1600_round0_theta_d_x3 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let c_x2_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 2 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let c_x4_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 4 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x2_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 2 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x4_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 4 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 3)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 3 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 3 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 0)
              (c_x2_zeta0 ^. (Core_models.Num.impl_u32__rotate_left c_x4_zeta1 (mk_u32 1) <: u32)
                <:
                u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 3)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 3 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 3 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 1)
              (c_x2_zeta1 ^. c_x4_zeta0 <: u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  s

let keccakf1600_round0_theta_d_x4 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let c_x3_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 3 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let c_x0_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 0 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x3_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 3 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x0_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 0 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 4)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 4 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 4 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 0)
              (c_x3_zeta0 ^. (Core_models.Num.impl_u32__rotate_left c_x0_zeta1 (mk_u32 1) <: u32)
                <:
                u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 4)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 4 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 4 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 1)
              (c_x3_zeta1 ^. c_x0_zeta0 <: u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  s

let keccakf1600_round0_theta_d (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round0_theta_d_x0 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round0_theta_d_x1 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round0_theta_d_x2 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round0_theta_d_x3 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round0_theta_d_x4 s in
  s

let keccakf1600_round0_theta (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round0_theta_c_x0_z0 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round0_theta_c_x0_z1 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round0_theta_c_x1_z0 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round0_theta_c_x1_z1 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round0_theta_c_x2_z0 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round0_theta_c_x2_z1 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round0_theta_c_x3_z0 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round0_theta_c_x3_z1 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round0_theta_c_x4_z0 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round0_theta_c_x4_z1 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round0_theta_d s in
  s

type t_BxArg = | BxArg : usize -> usize -> usize -> usize -> u32 -> t_BxArg

let impl_1: Core_models.Clone.t_Clone t_BxArg =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': Core_models.Marker.t_Copy t_BxArg

unfold
let impl_2 = impl_2'

let bx_2_ (s: Libcrux_iot_sha3.State.t_KeccakState) (a b: t_BxArg)
    : Prims.Pure (u32 & u32)
      (requires
        a._0 <. mk_usize 5 && a._1 <. mk_usize 5 && a._2 <. mk_usize 2 && a._3 <. mk_usize 2 &&
        b._0 <. mk_usize 5 &&
        b._1 <. mk_usize 5 &&
        b._2 <. mk_usize 2 &&
        b._3 <. mk_usize 2)
      (fun _ -> Prims.l_True) =
  Core_models.Num.impl_u32__rotate_left ((Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s
          a._0
          a._1
          a._2
        <:
        u32) ^.
      ((s.Libcrux_iot_sha3.State.f_d.[ a._1 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ a._3 ] <: u32)
      <:
      u32)
    a._4,
  Core_models.Num.impl_u32__rotate_left ((Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s
          b._0
          b._1
          b._2
        <:
        u32) ^.
      ((s.Libcrux_iot_sha3.State.f_d.[ b._1 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ b._3 ] <: u32)
      <:
      u32)
    b._4
  <:
  (u32 & u32)

let bx_3_ (s: Libcrux_iot_sha3.State.t_KeccakState) (a b c: t_BxArg)
    : Prims.Pure (u32 & u32 & u32)
      (requires
        a._0 <. mk_usize 5 && a._1 <. mk_usize 5 && a._2 <. mk_usize 2 && a._3 <. mk_usize 2 &&
        b._0 <. mk_usize 5 &&
        b._1 <. mk_usize 5 &&
        b._2 <. mk_usize 2 &&
        b._3 <. mk_usize 2 &&
        c._0 <. mk_usize 5 &&
        c._1 <. mk_usize 5 &&
        c._2 <. mk_usize 2 &&
        c._3 <. mk_usize 2)
      (fun _ -> Prims.l_True) =
  Core_models.Num.impl_u32__rotate_left ((Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s
          a._0
          a._1
          a._2
        <:
        u32) ^.
      ((s.Libcrux_iot_sha3.State.f_d.[ a._1 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ a._3 ] <: u32)
      <:
      u32)
    a._4,
  Core_models.Num.impl_u32__rotate_left ((Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s
          b._0
          b._1
          b._2
        <:
        u32) ^.
      ((s.Libcrux_iot_sha3.State.f_d.[ b._1 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ b._3 ] <: u32)
      <:
      u32)
    b._4,
  Core_models.Num.impl_u32__rotate_left ((Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s
          c._0
          c._1
          c._2
        <:
        u32) ^.
      ((s.Libcrux_iot_sha3.State.f_d.[ c._1 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ c._3 ] <: u32)
      <:
      u32)
    c._4
  <:
  (u32 & u32 & u32)

let keccakf1600_round0_pi_rho_chi_1a (v_BASE_ROUND: usize) (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Prims.Pure Libcrux_iot_sha3.State.t_KeccakState
      (requires v_BASE_ROUND <. mk_usize 255)
      (fun _ -> Prims.l_True) =
  let (bx0: u32), (bx1: u32) =
    bx_2_ s
      (BxArg (mk_usize 0) (mk_usize 0) (mk_usize 0) (mk_usize 0) (mk_u32 0) <: t_BxArg)
      (BxArg (mk_usize 1) (mk_usize 1) (mk_usize 0) (mk_usize 0) (mk_u32 22) <: t_BxArg)
  in
  let (bx2: u32), (bx3: u32), (bx4: u32) =
    bx_3_ s
      (BxArg (mk_usize 2) (mk_usize 2) (mk_usize 1) (mk_usize 1) (mk_u32 22) <: t_BxArg)
      (BxArg (mk_usize 3) (mk_usize 3) (mk_usize 1) (mk_usize 1) (mk_u32 11) <: t_BxArg)
      (BxArg (mk_usize 4) (mk_usize 4) (mk_usize 0) (mk_usize 0) (mk_u32 7) <: t_BxArg)
  in
  let ax0:u32 =
    (bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) <: u32) ^.
    (v_RC_INTERLEAVED_0_.[ v_BASE_ROUND +! mk_usize 0 <: usize ] <: u32)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 0)
      (mk_usize 0)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 1)
      (mk_usize 0)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 2)
      (mk_usize 1)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 3)
      (mk_usize 1)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 4)
      (mk_usize 0)
      ax4
  in
  s

let keccakf1600_round0_pi_rho_chi_1b (v_BASE_ROUND: usize) (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Prims.Pure Libcrux_iot_sha3.State.t_KeccakState
      (requires v_BASE_ROUND <. mk_usize 255)
      (fun _ -> Prims.l_True) =
  let (bx0: u32), (bx1: u32) =
    bx_2_ s
      (BxArg (mk_usize 0) (mk_usize 0) (mk_usize 1) (mk_usize 1) (mk_u32 0) <: t_BxArg)
      (BxArg (mk_usize 1) (mk_usize 1) (mk_usize 1) (mk_usize 1) (mk_u32 22) <: t_BxArg)
  in
  let (bx2: u32), (bx3: u32), (bx4: u32) =
    bx_3_ s
      (BxArg (mk_usize 2) (mk_usize 2) (mk_usize 0) (mk_usize 0) (mk_u32 21) <: t_BxArg)
      (BxArg (mk_usize 3) (mk_usize 3) (mk_usize 0) (mk_usize 0) (mk_u32 10) <: t_BxArg)
      (BxArg (mk_usize 4) (mk_usize 4) (mk_usize 1) (mk_usize 1) (mk_u32 7) <: t_BxArg)
  in
  let ax0:u32 =
    (bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) <: u32) ^.
    (v_RC_INTERLEAVED_1_.[ v_BASE_ROUND +! mk_usize 0 <: usize ] <: u32)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 0)
      (mk_usize 1)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 1)
      (mk_usize 1)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 2)
      (mk_usize 0)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 3)
      (mk_usize 0)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 4)
      (mk_usize 1)
      ax4
  in
  s

let keccakf1600_round0_pi_rho_chi_1c (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx4: u32), (bx0: u32), (bx1: u32) =
    bx_3_ s
      (BxArg (mk_usize 4) (mk_usize 2) (mk_usize 1) (mk_usize 1) (mk_u32 31) <: t_BxArg)
      (BxArg (mk_usize 0) (mk_usize 3) (mk_usize 0) (mk_usize 0) (mk_u32 14) <: t_BxArg)
      (BxArg (mk_usize 1) (mk_usize 4) (mk_usize 0) (mk_usize 0) (mk_u32 10) <: t_BxArg)
  in
  let (bx2: u32), (bx3: u32) =
    bx_2_ s
      (BxArg (mk_usize 2) (mk_usize 0) (mk_usize 1) (mk_usize 1) (mk_u32 2) <: t_BxArg)
      (BxArg (mk_usize 3) (mk_usize 1) (mk_usize 1) (mk_usize 1) (mk_u32 23) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 0)
      (mk_usize 1)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 1)
      (mk_usize 1)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 2)
      (mk_usize 1)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 3)
      (mk_usize 0)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 4)
      (mk_usize 0)
      ax4
  in
  s

let keccakf1600_round0_pi_rho_chi_1d (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx4: u32), (bx0: u32), (bx1: u32) =
    bx_3_ s
      (BxArg (mk_usize 4) (mk_usize 2) (mk_usize 0) (mk_usize 0) (mk_u32 30) <: t_BxArg)
      (BxArg (mk_usize 0) (mk_usize 3) (mk_usize 1) (mk_usize 1) (mk_u32 14) <: t_BxArg)
      (BxArg (mk_usize 1) (mk_usize 4) (mk_usize 1) (mk_usize 1) (mk_u32 10) <: t_BxArg)
  in
  let (bx2: u32), (bx3: u32) =
    bx_2_ s
      (BxArg (mk_usize 2) (mk_usize 0) (mk_usize 0) (mk_usize 0) (mk_u32 1) <: t_BxArg)
      (BxArg (mk_usize 3) (mk_usize 1) (mk_usize 0) (mk_usize 0) (mk_u32 22) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 0)
      (mk_usize 0)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 1)
      (mk_usize 0)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 2)
      (mk_usize 0)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 3)
      (mk_usize 1)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 4)
      (mk_usize 1)
      ax4
  in
  s

let keccakf1600_round0_pi_rho_chi_1_ (v_BASE_ROUND: usize) (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Prims.Pure Libcrux_iot_sha3.State.t_KeccakState
      (requires v_BASE_ROUND <. mk_usize 255)
      (fun _ -> Prims.l_True) =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round0_pi_rho_chi_1a v_BASE_ROUND s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round0_pi_rho_chi_1b v_BASE_ROUND s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round0_pi_rho_chi_1c s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round0_pi_rho_chi_1d s in
  s

let keccakf1600_round0_pi_rho_chi_2a (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx4: u32), (bx0: u32) =
    bx_2_ s
      (BxArg (mk_usize 4) (mk_usize 0) (mk_usize 0) (mk_usize 0) (mk_u32 9) <: t_BxArg)
      (BxArg (mk_usize 0) (mk_usize 1) (mk_usize 1) (mk_usize 1) (mk_u32 1) <: t_BxArg)
  in
  let (bx1: u32), (bx2: u32), (bx3: u32) =
    bx_3_ s
      (BxArg (mk_usize 1) (mk_usize 2) (mk_usize 0) (mk_usize 0) (mk_u32 3) <: t_BxArg)
      (BxArg (mk_usize 2) (mk_usize 3) (mk_usize 1) (mk_usize 1) (mk_u32 13) <: t_BxArg)
      (BxArg (mk_usize 3) (mk_usize 4) (mk_usize 0) (mk_usize 0) (mk_u32 4) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 0)
      (mk_usize 0)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 1)
      (mk_usize 1)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 2)
      (mk_usize 0)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 3)
      (mk_usize 1)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 4)
      (mk_usize 0)
      ax4
  in
  s

let keccakf1600_round0_pi_rho_chi_2b (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx4: u32), (bx0: u32) =
    bx_2_ s
      (BxArg (mk_usize 4) (mk_usize 0) (mk_usize 1) (mk_usize 1) (mk_u32 9) <: t_BxArg)
      (BxArg (mk_usize 0) (mk_usize 1) (mk_usize 0) (mk_usize 0) (mk_u32 0) <: t_BxArg)
  in
  let (bx1: u32), (bx2: u32), (bx3: u32) =
    bx_3_ s
      (BxArg (mk_usize 1) (mk_usize 2) (mk_usize 1) (mk_usize 1) (mk_u32 3) <: t_BxArg)
      (BxArg (mk_usize 2) (mk_usize 3) (mk_usize 0) (mk_usize 0) (mk_u32 12) <: t_BxArg)
      (BxArg (mk_usize 3) (mk_usize 4) (mk_usize 1) (mk_usize 1) (mk_u32 4) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 0)
      (mk_usize 1)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 1)
      (mk_usize 0)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 2)
      (mk_usize 1)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 3)
      (mk_usize 0)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 4)
      (mk_usize 1)
      ax4
  in
  s

let keccakf1600_round0_pi_rho_chi_2c (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx1: u32), (bx2: u32) =
    bx_2_ s
      (BxArg (mk_usize 1) (mk_usize 0) (mk_usize 0) (mk_usize 0) (mk_u32 18) <: t_BxArg)
      (BxArg (mk_usize 2) (mk_usize 1) (mk_usize 0) (mk_usize 0) (mk_u32 5) <: t_BxArg)
  in
  let (bx3: u32), (bx4: u32), (bx0: u32) =
    bx_3_ s
      (BxArg (mk_usize 3) (mk_usize 2) (mk_usize 1) (mk_usize 1) (mk_u32 8) <: t_BxArg)
      (BxArg (mk_usize 4) (mk_usize 3) (mk_usize 0) (mk_usize 0) (mk_u32 28) <: t_BxArg)
      (BxArg (mk_usize 0) (mk_usize 4) (mk_usize 1) (mk_usize 1) (mk_u32 14) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 0)
      (mk_usize 0)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 1)
      (mk_usize 0)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 2)
      (mk_usize 1)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 3)
      (mk_usize 0)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 4)
      (mk_usize 1)
      ax4
  in
  s

let keccakf1600_round0_pi_rho_chi_2d (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx1: u32), (bx2: u32) =
    bx_2_ s
      (BxArg (mk_usize 1) (mk_usize 0) (mk_usize 1) (mk_usize 1) (mk_u32 18) <: t_BxArg)
      (BxArg (mk_usize 2) (mk_usize 1) (mk_usize 1) (mk_usize 1) (mk_u32 5) <: t_BxArg)
  in
  let (bx3: u32), (bx4: u32), (bx0: u32) =
    bx_3_ s
      (BxArg (mk_usize 3) (mk_usize 2) (mk_usize 0) (mk_usize 0) (mk_u32 7) <: t_BxArg)
      (BxArg (mk_usize 4) (mk_usize 3) (mk_usize 1) (mk_usize 1) (mk_u32 28) <: t_BxArg)
      (BxArg (mk_usize 0) (mk_usize 4) (mk_usize 0) (mk_usize 0) (mk_u32 13) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 0)
      (mk_usize 1)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 1)
      (mk_usize 1)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 2)
      (mk_usize 0)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 3)
      (mk_usize 1)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 4)
      (mk_usize 0)
      ax4
  in
  s

let keccakf1600_round0_pi_rho_chi_2e (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx0: u32), (bx1: u32), (bx2: u32) =
    bx_3_ s
      (BxArg (mk_usize 0) (mk_usize 2) (mk_usize 0) (mk_usize 0) (mk_u32 31) <: t_BxArg)
      (BxArg (mk_usize 1) (mk_usize 3) (mk_usize 1) (mk_usize 1) (mk_u32 28) <: t_BxArg)
      (BxArg (mk_usize 2) (mk_usize 4) (mk_usize 1) (mk_usize 1) (mk_u32 20) <: t_BxArg)
  in
  let (bx3: u32), (bx4: u32) =
    bx_2_ s
      (BxArg (mk_usize 3) (mk_usize 0) (mk_usize 1) (mk_usize 1) (mk_u32 21) <: t_BxArg)
      (BxArg (mk_usize 4) (mk_usize 1) (mk_usize 0) (mk_usize 0) (mk_u32 1) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 0)
      (mk_usize 1)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 1)
      (mk_usize 0)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 2)
      (mk_usize 0)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 3)
      (mk_usize 1)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 4)
      (mk_usize 1)
      ax4
  in
  s

let keccakf1600_round0_pi_rho_chi_2f (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx0: u32), (bx1: u32), (bx2: u32) =
    bx_3_ s
      (BxArg (mk_usize 0) (mk_usize 2) (mk_usize 1) (mk_usize 1) (mk_u32 31) <: t_BxArg)
      (BxArg (mk_usize 1) (mk_usize 3) (mk_usize 0) (mk_usize 0) (mk_u32 27) <: t_BxArg)
      (BxArg (mk_usize 2) (mk_usize 4) (mk_usize 0) (mk_usize 0) (mk_u32 19) <: t_BxArg)
  in
  let (bx3: u32), (bx4: u32) =
    bx_2_ s
      (BxArg (mk_usize 3) (mk_usize 0) (mk_usize 0) (mk_usize 0) (mk_u32 20) <: t_BxArg)
      (BxArg (mk_usize 4) (mk_usize 1) (mk_usize 1) (mk_usize 1) (mk_u32 1) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 0)
      (mk_usize 0)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 1)
      (mk_usize 1)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 2)
      (mk_usize 1)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 3)
      (mk_usize 0)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 4)
      (mk_usize 0)
      ax4
  in
  s

let keccakf1600_round0_pi_rho_chi_2_ (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round0_pi_rho_chi_2a s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round0_pi_rho_chi_2b s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round0_pi_rho_chi_2c s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round0_pi_rho_chi_2d s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round0_pi_rho_chi_2e s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round0_pi_rho_chi_2f s in
  s

let keccakf1600_round1_theta_c_x0_z0 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 0) (mk_usize 0)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 0) (mk_usize 1)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 0) (mk_usize 0)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 0) (mk_usize 0)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 0) (mk_usize 1)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 0)
      (mk_usize 0)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round1_theta_c_x0_z1 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 0) (mk_usize 1)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 0) (mk_usize 0)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 0) (mk_usize 1)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 0) (mk_usize 1)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 0) (mk_usize 0)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 0)
      (mk_usize 1)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round1_theta_c_x1_z0 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 1) (mk_usize 0)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 1) (mk_usize 1)
  in
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 1) (mk_usize 1)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 1) (mk_usize 0)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 1) (mk_usize 0)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 1)
      (mk_usize 0)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round1_theta_c_x1_z1 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 1) (mk_usize 1)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 1) (mk_usize 0)
  in
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 1) (mk_usize 0)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 1) (mk_usize 1)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 1) (mk_usize 1)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 1)
      (mk_usize 1)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round1_theta_c_x2_z0 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 2) (mk_usize 1)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 2) (mk_usize 1)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 2) (mk_usize 0)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 2) (mk_usize 1)
  in
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 2) (mk_usize 0)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 2)
      (mk_usize 0)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round1_theta_c_x2_z1 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 2) (mk_usize 0)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 2) (mk_usize 0)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 2) (mk_usize 1)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 2) (mk_usize 0)
  in
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 2) (mk_usize 1)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 2)
      (mk_usize 1)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round1_theta_c_x3_z0 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 3) (mk_usize 1)
  in
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 3) (mk_usize 0)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 3) (mk_usize 1)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 3) (mk_usize 0)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 3) (mk_usize 1)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 3)
      (mk_usize 0)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round1_theta_c_x3_z1 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 3) (mk_usize 0)
  in
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 3) (mk_usize 1)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 3) (mk_usize 0)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 3) (mk_usize 1)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 3) (mk_usize 0)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 3)
      (mk_usize 1)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round1_theta_c_x4_z0 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 4) (mk_usize 0)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 4) (mk_usize 0)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 4) (mk_usize 0)
  in
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 4) (mk_usize 1)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 4) (mk_usize 1)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 4)
      (mk_usize 0)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round1_theta_c_x4_z1 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 4) (mk_usize 1)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 4) (mk_usize 1)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 4) (mk_usize 1)
  in
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 4) (mk_usize 0)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 4) (mk_usize 0)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 4)
      (mk_usize 1)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round1_theta_d_x0 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let c_x4_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 4 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let c_x1_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 1 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x4_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 4 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x1_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 1 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 0)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 0 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 0 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 0)
              (c_x4_zeta0 ^. (Core_models.Num.impl_u32__rotate_left c_x1_zeta1 (mk_u32 1) <: u32)
                <:
                u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 0)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 0 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 0 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 1)
              (c_x4_zeta1 ^. c_x1_zeta0 <: u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  s

let keccakf1600_round1_theta_d_x1 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let c_x0_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 0 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let c_x2_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 2 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x0_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 0 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x2_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 2 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 1)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 1 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 1 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 0)
              (c_x0_zeta0 ^. (Core_models.Num.impl_u32__rotate_left c_x2_zeta1 (mk_u32 1) <: u32)
                <:
                u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 1)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 1 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 1 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 1)
              (c_x0_zeta1 ^. c_x2_zeta0 <: u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  s

let keccakf1600_round1_theta_d_x2 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let c_x1_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 1 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let c_x3_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 3 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x1_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 1 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x3_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 3 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 2)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 2 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 2 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 0)
              (c_x1_zeta0 ^. (Core_models.Num.impl_u32__rotate_left c_x3_zeta1 (mk_u32 1) <: u32)
                <:
                u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 2)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 2 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 2 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 1)
              (c_x1_zeta1 ^. c_x3_zeta0 <: u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  s

let keccakf1600_round1_theta_d_x3 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let c_x2_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 2 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let c_x4_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 4 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x2_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 2 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x4_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 4 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 3)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 3 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 3 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 0)
              (c_x2_zeta0 ^. (Core_models.Num.impl_u32__rotate_left c_x4_zeta1 (mk_u32 1) <: u32)
                <:
                u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 3)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 3 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 3 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 1)
              (c_x2_zeta1 ^. c_x4_zeta0 <: u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  s

let keccakf1600_round1_theta_d_x4 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let c_x3_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 3 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let c_x0_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 0 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x3_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 3 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x0_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 0 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 4)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 4 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 4 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 0)
              (c_x3_zeta0 ^. (Core_models.Num.impl_u32__rotate_left c_x0_zeta1 (mk_u32 1) <: u32)
                <:
                u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 4)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 4 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 4 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 1)
              (c_x3_zeta1 ^. c_x0_zeta0 <: u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  s

let keccakf1600_round1_theta_d (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round1_theta_d_x0 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round1_theta_d_x1 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round1_theta_d_x2 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round1_theta_d_x3 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round1_theta_d_x4 s in
  s

let keccakf1600_round1_theta (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round1_theta_c_x0_z0 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round1_theta_c_x0_z1 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round1_theta_c_x1_z0 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round1_theta_c_x1_z1 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round1_theta_c_x2_z0 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round1_theta_c_x2_z1 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round1_theta_c_x3_z0 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round1_theta_c_x3_z1 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round1_theta_c_x4_z0 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round1_theta_c_x4_z1 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round1_theta_d s in
  s

let keccakf1600_round1_pi_rho_chi_1a (v_BASE_ROUND: usize) (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Prims.Pure Libcrux_iot_sha3.State.t_KeccakState
      (requires v_BASE_ROUND <. mk_usize 254)
      (fun _ -> Prims.l_True) =
  let (bx0: u32), (bx1: u32) =
    bx_2_ s
      (BxArg (mk_usize 0) (mk_usize 0) (mk_usize 0) (mk_usize 0) (mk_u32 0) <: t_BxArg)
      (BxArg (mk_usize 3) (mk_usize 1) (mk_usize 1) (mk_usize 0) (mk_u32 22) <: t_BxArg)
  in
  let (bx2: u32), (bx3: u32), (bx4: u32) =
    bx_3_ s
      (BxArg (mk_usize 1) (mk_usize 2) (mk_usize 1) (mk_usize 1) (mk_u32 22) <: t_BxArg)
      (BxArg (mk_usize 4) (mk_usize 3) (mk_usize 1) (mk_usize 1) (mk_u32 11) <: t_BxArg)
      (BxArg (mk_usize 2) (mk_usize 4) (mk_usize 1) (mk_usize 0) (mk_u32 7) <: t_BxArg)
  in
  let ax0:u32 =
    (bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) <: u32) ^.
    (v_RC_INTERLEAVED_0_.[ v_BASE_ROUND +! mk_usize 1 <: usize ] <: u32)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 0)
      (mk_usize 0)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 1)
      (mk_usize 1)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 2)
      (mk_usize 1)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 3)
      (mk_usize 1)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 4)
      (mk_usize 1)
      ax4
  in
  s

let keccakf1600_round1_pi_rho_chi_1b (v_BASE_ROUND: usize) (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Prims.Pure Libcrux_iot_sha3.State.t_KeccakState
      (requires v_BASE_ROUND <. mk_usize 254)
      (fun _ -> Prims.l_True) =
  let (bx0: u32), (bx1: u32) =
    bx_2_ s
      (BxArg (mk_usize 0) (mk_usize 0) (mk_usize 1) (mk_usize 1) (mk_u32 0) <: t_BxArg)
      (BxArg (mk_usize 3) (mk_usize 1) (mk_usize 0) (mk_usize 1) (mk_u32 22) <: t_BxArg)
  in
  let (bx2: u32), (bx3: u32), (bx4: u32) =
    bx_3_ s
      (BxArg (mk_usize 1) (mk_usize 2) (mk_usize 0) (mk_usize 0) (mk_u32 21) <: t_BxArg)
      (BxArg (mk_usize 4) (mk_usize 3) (mk_usize 0) (mk_usize 0) (mk_u32 10) <: t_BxArg)
      (BxArg (mk_usize 2) (mk_usize 4) (mk_usize 0) (mk_usize 1) (mk_u32 7) <: t_BxArg)
  in
  let ax0:u32 =
    (bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) <: u32) ^.
    (v_RC_INTERLEAVED_1_.[ v_BASE_ROUND +! mk_usize 1 <: usize ] <: u32)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 0)
      (mk_usize 1)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 1)
      (mk_usize 0)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 2)
      (mk_usize 0)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 3)
      (mk_usize 0)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 4)
      (mk_usize 0)
      ax4
  in
  s

let keccakf1600_round1_pi_rho_chi_1c (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx4: u32), (bx0: u32), (bx1: u32) =
    bx_3_ s
      (BxArg (mk_usize 0) (mk_usize 2) (mk_usize 1) (mk_usize 1) (mk_u32 31) <: t_BxArg)
      (BxArg (mk_usize 3) (mk_usize 3) (mk_usize 1) (mk_usize 0) (mk_u32 14) <: t_BxArg)
      (BxArg (mk_usize 1) (mk_usize 4) (mk_usize 0) (mk_usize 0) (mk_u32 10) <: t_BxArg)
  in
  let (bx2: u32), (bx3: u32) =
    bx_2_ s
      (BxArg (mk_usize 4) (mk_usize 0) (mk_usize 1) (mk_usize 1) (mk_u32 2) <: t_BxArg)
      (BxArg (mk_usize 2) (mk_usize 1) (mk_usize 1) (mk_usize 1) (mk_u32 23) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 0)
      (mk_usize 1)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 1)
      (mk_usize 1)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 2)
      (mk_usize 1)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 3)
      (mk_usize 1)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 4)
      (mk_usize 0)
      ax4
  in
  s

let keccakf1600_round1_pi_rho_chi_1d (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx4: u32), (bx0: u32), (bx1: u32) =
    bx_3_ s
      (BxArg (mk_usize 0) (mk_usize 2) (mk_usize 0) (mk_usize 0) (mk_u32 30) <: t_BxArg)
      (BxArg (mk_usize 3) (mk_usize 3) (mk_usize 0) (mk_usize 1) (mk_u32 14) <: t_BxArg)
      (BxArg (mk_usize 1) (mk_usize 4) (mk_usize 1) (mk_usize 1) (mk_u32 10) <: t_BxArg)
  in
  let (bx2: u32), (bx3: u32) =
    bx_2_ s
      (BxArg (mk_usize 4) (mk_usize 0) (mk_usize 0) (mk_usize 0) (mk_u32 1) <: t_BxArg)
      (BxArg (mk_usize 2) (mk_usize 1) (mk_usize 0) (mk_usize 0) (mk_u32 22) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 0)
      (mk_usize 0)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 1)
      (mk_usize 0)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 2)
      (mk_usize 0)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 3)
      (mk_usize 0)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 4)
      (mk_usize 1)
      ax4
  in
  s

let keccakf1600_round1_pi_rho_chi_1_ (v_BASE_ROUND: usize) (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Prims.Pure Libcrux_iot_sha3.State.t_KeccakState
      (requires v_BASE_ROUND <. mk_usize 254)
      (fun _ -> Prims.l_True) =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round1_pi_rho_chi_1a v_BASE_ROUND s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round1_pi_rho_chi_1b v_BASE_ROUND s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round1_pi_rho_chi_1c s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round1_pi_rho_chi_1d s in
  s

let keccakf1600_round1_pi_rho_chi_2a (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx4: u32), (bx0: u32) =
    bx_2_ s
      (BxArg (mk_usize 3) (mk_usize 0) (mk_usize 1) (mk_usize 0) (mk_u32 9) <: t_BxArg)
      (BxArg (mk_usize 1) (mk_usize 1) (mk_usize 1) (mk_usize 1) (mk_u32 1) <: t_BxArg)
  in
  let (bx1: u32), (bx2: u32), (bx3: u32) =
    bx_3_ s
      (BxArg (mk_usize 4) (mk_usize 2) (mk_usize 1) (mk_usize 0) (mk_u32 3) <: t_BxArg)
      (BxArg (mk_usize 2) (mk_usize 3) (mk_usize 0) (mk_usize 1) (mk_u32 13) <: t_BxArg)
      (BxArg (mk_usize 0) (mk_usize 4) (mk_usize 1) (mk_usize 0) (mk_u32 4) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 0)
      (mk_usize 1)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 1)
      (mk_usize 1)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 2)
      (mk_usize 1)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 3)
      (mk_usize 0)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 4)
      (mk_usize 1)
      ax4
  in
  s

let keccakf1600_round1_pi_rho_chi_2b (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx4: u32), (bx0: u32) =
    bx_2_ s
      (BxArg (mk_usize 3) (mk_usize 0) (mk_usize 0) (mk_usize 1) (mk_u32 9) <: t_BxArg)
      (BxArg (mk_usize 1) (mk_usize 1) (mk_usize 0) (mk_usize 0) (mk_u32 0) <: t_BxArg)
  in
  let (bx1: u32), (bx2: u32), (bx3: u32) =
    bx_3_ s
      (BxArg (mk_usize 4) (mk_usize 2) (mk_usize 0) (mk_usize 1) (mk_u32 3) <: t_BxArg)
      (BxArg (mk_usize 2) (mk_usize 3) (mk_usize 1) (mk_usize 0) (mk_u32 12) <: t_BxArg)
      (BxArg (mk_usize 0) (mk_usize 4) (mk_usize 0) (mk_usize 1) (mk_u32 4) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 0)
      (mk_usize 0)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 1)
      (mk_usize 0)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 2)
      (mk_usize 0)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 3)
      (mk_usize 1)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 4)
      (mk_usize 0)
      ax4
  in
  s

let keccakf1600_round1_pi_rho_chi_2c (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx1: u32), (bx2: u32) =
    bx_2_ s
      (BxArg (mk_usize 2) (mk_usize 0) (mk_usize 1) (mk_usize 0) (mk_u32 18) <: t_BxArg)
      (BxArg (mk_usize 0) (mk_usize 1) (mk_usize 1) (mk_usize 0) (mk_u32 5) <: t_BxArg)
  in
  let (bx3: u32), (bx4: u32), (bx0: u32) =
    bx_3_ s
      (BxArg (mk_usize 3) (mk_usize 2) (mk_usize 0) (mk_usize 1) (mk_u32 8) <: t_BxArg)
      (BxArg (mk_usize 1) (mk_usize 3) (mk_usize 1) (mk_usize 0) (mk_u32 28) <: t_BxArg)
      (BxArg (mk_usize 4) (mk_usize 4) (mk_usize 1) (mk_usize 1) (mk_u32 14) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 0)
      (mk_usize 1)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 1)
      (mk_usize 1)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 2)
      (mk_usize 0)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 3)
      (mk_usize 1)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 4)
      (mk_usize 1)
      ax4
  in
  s

let keccakf1600_round1_pi_rho_chi_2d (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx1: u32), (bx2: u32) =
    bx_2_ s
      (BxArg (mk_usize 2) (mk_usize 0) (mk_usize 0) (mk_usize 1) (mk_u32 18) <: t_BxArg)
      (BxArg (mk_usize 0) (mk_usize 1) (mk_usize 0) (mk_usize 1) (mk_u32 5) <: t_BxArg)
  in
  let (bx3: u32), (bx4: u32), (bx0: u32) =
    bx_3_ s
      (BxArg (mk_usize 3) (mk_usize 2) (mk_usize 1) (mk_usize 0) (mk_u32 7) <: t_BxArg)
      (BxArg (mk_usize 1) (mk_usize 3) (mk_usize 0) (mk_usize 1) (mk_u32 28) <: t_BxArg)
      (BxArg (mk_usize 4) (mk_usize 4) (mk_usize 0) (mk_usize 0) (mk_u32 13) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 0)
      (mk_usize 0)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 1)
      (mk_usize 0)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 2)
      (mk_usize 1)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 3)
      (mk_usize 0)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 4)
      (mk_usize 0)
      ax4
  in
  s

let keccakf1600_round1_pi_rho_chi_2e (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx0: u32), (bx1: u32), (bx2: u32) =
    bx_3_ s
      (BxArg (mk_usize 2) (mk_usize 2) (mk_usize 1) (mk_usize 0) (mk_u32 31) <: t_BxArg)
      (BxArg (mk_usize 0) (mk_usize 3) (mk_usize 1) (mk_usize 1) (mk_u32 28) <: t_BxArg)
      (BxArg (mk_usize 3) (mk_usize 4) (mk_usize 1) (mk_usize 1) (mk_u32 20) <: t_BxArg)
  in
  let (bx3: u32), (bx4: u32) =
    bx_2_ s
      (BxArg (mk_usize 1) (mk_usize 0) (mk_usize 1) (mk_usize 1) (mk_u32 21) <: t_BxArg)
      (BxArg (mk_usize 4) (mk_usize 1) (mk_usize 0) (mk_usize 0) (mk_u32 1) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 0)
      (mk_usize 1)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 1)
      (mk_usize 0)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 2)
      (mk_usize 1)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 3)
      (mk_usize 1)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 4)
      (mk_usize 1)
      ax4
  in
  s

let keccakf1600_round1_pi_rho_chi_2f (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx0: u32), (bx1: u32), (bx2: u32) =
    bx_3_ s
      (BxArg (mk_usize 2) (mk_usize 2) (mk_usize 0) (mk_usize 1) (mk_u32 31) <: t_BxArg)
      (BxArg (mk_usize 0) (mk_usize 3) (mk_usize 0) (mk_usize 0) (mk_u32 27) <: t_BxArg)
      (BxArg (mk_usize 3) (mk_usize 4) (mk_usize 0) (mk_usize 0) (mk_u32 19) <: t_BxArg)
  in
  let (bx3: u32), (bx4: u32) =
    bx_2_ s
      (BxArg (mk_usize 1) (mk_usize 0) (mk_usize 0) (mk_usize 0) (mk_u32 20) <: t_BxArg)
      (BxArg (mk_usize 4) (mk_usize 1) (mk_usize 1) (mk_usize 1) (mk_u32 1) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 0)
      (mk_usize 0)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 1)
      (mk_usize 1)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 2)
      (mk_usize 0)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 3)
      (mk_usize 0)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 4)
      (mk_usize 0)
      ax4
  in
  s

let keccakf1600_round1_pi_rho_chi_2_ (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round1_pi_rho_chi_2a s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round1_pi_rho_chi_2b s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round1_pi_rho_chi_2c s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round1_pi_rho_chi_2d s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round1_pi_rho_chi_2e s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round1_pi_rho_chi_2f s in
  s

let keccakf1600_round2_theta_c_x0_z0 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 0) (mk_usize 0)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 0) (mk_usize 1)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 0) (mk_usize 1)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 0) (mk_usize 1)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 0) (mk_usize 1)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 0)
      (mk_usize 0)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round2_theta_c_x0_z1 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 0) (mk_usize 1)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 0) (mk_usize 0)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 0) (mk_usize 0)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 0) (mk_usize 0)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 0) (mk_usize 0)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 0)
      (mk_usize 1)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round2_theta_c_x1_z0 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 1) (mk_usize 1)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 1) (mk_usize 1)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 1) (mk_usize 1)
  in
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 1) (mk_usize 1)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 1) (mk_usize 0)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 1)
      (mk_usize 0)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round2_theta_c_x1_z1 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 1) (mk_usize 0)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 1) (mk_usize 0)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 1) (mk_usize 0)
  in
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 1) (mk_usize 0)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 1) (mk_usize 1)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 1)
      (mk_usize 1)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round2_theta_c_x2_z0 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 2) (mk_usize 1)
  in
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 2) (mk_usize 1)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 2) (mk_usize 1)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 2) (mk_usize 0)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 2) (mk_usize 1)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 2)
      (mk_usize 0)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round2_theta_c_x2_z1 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 2) (mk_usize 0)
  in
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 2) (mk_usize 0)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 2) (mk_usize 0)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 2) (mk_usize 1)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 2) (mk_usize 0)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 2)
      (mk_usize 1)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round2_theta_c_x3_z0 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 3) (mk_usize 1)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 3) (mk_usize 1)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 3) (mk_usize 0)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 3) (mk_usize 1)
  in
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 3) (mk_usize 1)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 3)
      (mk_usize 0)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round2_theta_c_x3_z1 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 3) (mk_usize 0)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 3) (mk_usize 0)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 3) (mk_usize 1)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 3) (mk_usize 0)
  in
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 3) (mk_usize 0)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 3)
      (mk_usize 1)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round2_theta_c_x4_z0 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 4) (mk_usize 1)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 4) (mk_usize 0)
  in
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 4) (mk_usize 1)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 4) (mk_usize 1)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 4) (mk_usize 1)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 4)
      (mk_usize 0)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round2_theta_c_x4_z1 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 4) (mk_usize 0)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 4) (mk_usize 1)
  in
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 4) (mk_usize 0)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 4) (mk_usize 0)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 4) (mk_usize 0)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 4)
      (mk_usize 1)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round2_theta_d_x0 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let c_x4_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 4 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let c_x1_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 1 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x4_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 4 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x1_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 1 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 0)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 0 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 0 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 0)
              (c_x4_zeta0 ^. (Core_models.Num.impl_u32__rotate_left c_x1_zeta1 (mk_u32 1) <: u32)
                <:
                u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 0)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 0 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 0 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 1)
              (c_x4_zeta1 ^. c_x1_zeta0 <: u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  s

let keccakf1600_round2_theta_d_x1 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let c_x0_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 0 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let c_x2_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 2 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x0_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 0 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x2_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 2 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 1)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 1 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 1 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 0)
              (c_x0_zeta0 ^. (Core_models.Num.impl_u32__rotate_left c_x2_zeta1 (mk_u32 1) <: u32)
                <:
                u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 1)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 1 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 1 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 1)
              (c_x0_zeta1 ^. c_x2_zeta0 <: u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  s

let keccakf1600_round2_theta_d_x2 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let c_x1_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 1 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let c_x3_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 3 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x1_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 1 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x3_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 3 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 2)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 2 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 2 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 0)
              (c_x1_zeta0 ^. (Core_models.Num.impl_u32__rotate_left c_x3_zeta1 (mk_u32 1) <: u32)
                <:
                u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 2)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 2 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 2 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 1)
              (c_x1_zeta1 ^. c_x3_zeta0 <: u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  s

let keccakf1600_round2_theta_d_x3 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let c_x2_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 2 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let c_x4_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 4 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x2_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 2 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x4_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 4 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 3)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 3 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 3 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 0)
              (c_x2_zeta0 ^. (Core_models.Num.impl_u32__rotate_left c_x4_zeta1 (mk_u32 1) <: u32)
                <:
                u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 3)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 3 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 3 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 1)
              (c_x2_zeta1 ^. c_x4_zeta0 <: u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  s

let keccakf1600_round2_theta_d_x4 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let c_x3_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 3 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let c_x0_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 0 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x3_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 3 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x0_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 0 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 4)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 4 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 4 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 0)
              (c_x3_zeta0 ^. (Core_models.Num.impl_u32__rotate_left c_x0_zeta1 (mk_u32 1) <: u32)
                <:
                u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 4)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 4 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 4 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 1)
              (c_x3_zeta1 ^. c_x0_zeta0 <: u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  s

let keccakf1600_round2_theta_d (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round2_theta_d_x0 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round2_theta_d_x1 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round2_theta_d_x2 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round2_theta_d_x3 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round2_theta_d_x4 s in
  s

let keccakf1600_round2_theta (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round2_theta_c_x0_z0 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round2_theta_c_x0_z1 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round2_theta_c_x1_z0 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round2_theta_c_x1_z1 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round2_theta_c_x2_z0 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round2_theta_c_x2_z1 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round2_theta_c_x3_z0 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round2_theta_c_x3_z1 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round2_theta_c_x4_z0 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round2_theta_c_x4_z1 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round2_theta_d s in
  s

let keccakf1600_round2_pi_rho_chi_1a (v_BASE_ROUND: usize) (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Prims.Pure Libcrux_iot_sha3.State.t_KeccakState
      (requires v_BASE_ROUND <. mk_usize 253)
      (fun _ -> Prims.l_True) =
  let (bx0: u32), (bx1: u32) =
    bx_2_ s
      (BxArg (mk_usize 0) (mk_usize 0) (mk_usize 0) (mk_usize 0) (mk_u32 0) <: t_BxArg)
      (BxArg (mk_usize 2) (mk_usize 1) (mk_usize 1) (mk_usize 0) (mk_u32 22) <: t_BxArg)
  in
  let (bx2: u32), (bx3: u32), (bx4: u32) =
    bx_3_ s
      (BxArg (mk_usize 4) (mk_usize 2) (mk_usize 0) (mk_usize 1) (mk_u32 22) <: t_BxArg)
      (BxArg (mk_usize 1) (mk_usize 3) (mk_usize 0) (mk_usize 1) (mk_u32 11) <: t_BxArg)
      (BxArg (mk_usize 3) (mk_usize 4) (mk_usize 1) (mk_usize 0) (mk_u32 7) <: t_BxArg)
  in
  let ax0:u32 =
    (bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) <: u32) ^.
    (v_RC_INTERLEAVED_0_.[ v_BASE_ROUND +! mk_usize 2 <: usize ] <: u32)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 0)
      (mk_usize 0)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 1)
      (mk_usize 1)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 2)
      (mk_usize 0)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 3)
      (mk_usize 0)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 4)
      (mk_usize 1)
      ax4
  in
  s

let keccakf1600_round2_pi_rho_chi_1b (v_BASE_ROUND: usize) (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Prims.Pure Libcrux_iot_sha3.State.t_KeccakState
      (requires v_BASE_ROUND <. mk_usize 253)
      (fun _ -> Prims.l_True) =
  let (bx0: u32), (bx1: u32) =
    bx_2_ s
      (BxArg (mk_usize 0) (mk_usize 0) (mk_usize 1) (mk_usize 1) (mk_u32 0) <: t_BxArg)
      (BxArg (mk_usize 2) (mk_usize 1) (mk_usize 0) (mk_usize 1) (mk_u32 22) <: t_BxArg)
  in
  let (bx2: u32), (bx3: u32), (bx4: u32) =
    bx_3_ s
      (BxArg (mk_usize 4) (mk_usize 2) (mk_usize 1) (mk_usize 0) (mk_u32 21) <: t_BxArg)
      (BxArg (mk_usize 1) (mk_usize 3) (mk_usize 1) (mk_usize 0) (mk_u32 10) <: t_BxArg)
      (BxArg (mk_usize 3) (mk_usize 4) (mk_usize 0) (mk_usize 1) (mk_u32 7) <: t_BxArg)
  in
  let ax0:u32 =
    (bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) <: u32) ^.
    (v_RC_INTERLEAVED_1_.[ v_BASE_ROUND +! mk_usize 2 <: usize ] <: u32)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 0)
      (mk_usize 1)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 1)
      (mk_usize 0)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 2)
      (mk_usize 1)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 3)
      (mk_usize 1)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 4)
      (mk_usize 0)
      ax4
  in
  s

let keccakf1600_round2_pi_rho_chi_1c (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx4: u32), (bx0: u32), (bx1: u32) =
    bx_3_ s
      (BxArg (mk_usize 2) (mk_usize 2) (mk_usize 0) (mk_usize 1) (mk_u32 31) <: t_BxArg)
      (BxArg (mk_usize 4) (mk_usize 3) (mk_usize 1) (mk_usize 0) (mk_u32 14) <: t_BxArg)
      (BxArg (mk_usize 1) (mk_usize 4) (mk_usize 0) (mk_usize 0) (mk_u32 10) <: t_BxArg)
  in
  let (bx2: u32), (bx3: u32) =
    bx_2_ s
      (BxArg (mk_usize 3) (mk_usize 0) (mk_usize 0) (mk_usize 1) (mk_u32 2) <: t_BxArg)
      (BxArg (mk_usize 0) (mk_usize 1) (mk_usize 0) (mk_usize 1) (mk_u32 23) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 0)
      (mk_usize 0)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 1)
      (mk_usize 0)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 2)
      (mk_usize 0)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 3)
      (mk_usize 1)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 4)
      (mk_usize 0)
      ax4
  in
  s

let keccakf1600_round2_pi_rho_chi_1d (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx4: u32), (bx0: u32), (bx1: u32) =
    bx_3_ s
      (BxArg (mk_usize 2) (mk_usize 2) (mk_usize 1) (mk_usize 0) (mk_u32 30) <: t_BxArg)
      (BxArg (mk_usize 4) (mk_usize 3) (mk_usize 0) (mk_usize 1) (mk_u32 14) <: t_BxArg)
      (BxArg (mk_usize 1) (mk_usize 4) (mk_usize 1) (mk_usize 1) (mk_u32 10) <: t_BxArg)
  in
  let (bx2: u32), (bx3: u32) =
    bx_2_ s
      (BxArg (mk_usize 3) (mk_usize 0) (mk_usize 1) (mk_usize 0) (mk_u32 1) <: t_BxArg)
      (BxArg (mk_usize 0) (mk_usize 1) (mk_usize 1) (mk_usize 0) (mk_u32 22) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 0)
      (mk_usize 1)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 1)
      (mk_usize 1)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 2)
      (mk_usize 1)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 3)
      (mk_usize 0)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 4)
      (mk_usize 1)
      ax4
  in
  s

let keccakf1600_round2_pi_rho_chi_1_ (v_BASE_ROUND: usize) (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Prims.Pure Libcrux_iot_sha3.State.t_KeccakState
      (requires v_BASE_ROUND <. mk_usize 253)
      (fun _ -> Prims.l_True) =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round2_pi_rho_chi_1a v_BASE_ROUND s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round2_pi_rho_chi_1b v_BASE_ROUND s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round2_pi_rho_chi_1c s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round2_pi_rho_chi_1d s in
  s

let keccakf1600_round2_pi_rho_chi_2a (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx4: u32), (bx0: u32) =
    bx_2_ s
      (BxArg (mk_usize 1) (mk_usize 0) (mk_usize 1) (mk_usize 0) (mk_u32 9) <: t_BxArg)
      (BxArg (mk_usize 3) (mk_usize 1) (mk_usize 0) (mk_usize 1) (mk_u32 1) <: t_BxArg)
  in
  let (bx1: u32), (bx2: u32), (bx3: u32) =
    bx_3_ s
      (BxArg (mk_usize 0) (mk_usize 2) (mk_usize 1) (mk_usize 0) (mk_u32 3) <: t_BxArg)
      (BxArg (mk_usize 2) (mk_usize 3) (mk_usize 1) (mk_usize 1) (mk_u32 13) <: t_BxArg)
      (BxArg (mk_usize 4) (mk_usize 4) (mk_usize 1) (mk_usize 0) (mk_u32 4) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 0)
      (mk_usize 1)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 1)
      (mk_usize 0)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 2)
      (mk_usize 1)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 3)
      (mk_usize 1)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 4)
      (mk_usize 1)
      ax4
  in
  s

let keccakf1600_round2_pi_rho_chi_2b (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx4: u32), (bx0: u32) =
    bx_2_ s
      (BxArg (mk_usize 1) (mk_usize 0) (mk_usize 0) (mk_usize 1) (mk_u32 9) <: t_BxArg)
      (BxArg (mk_usize 3) (mk_usize 1) (mk_usize 1) (mk_usize 0) (mk_u32 0) <: t_BxArg)
  in
  let (bx1: u32), (bx2: u32), (bx3: u32) =
    bx_3_ s
      (BxArg (mk_usize 0) (mk_usize 2) (mk_usize 0) (mk_usize 1) (mk_u32 3) <: t_BxArg)
      (BxArg (mk_usize 2) (mk_usize 3) (mk_usize 0) (mk_usize 0) (mk_u32 12) <: t_BxArg)
      (BxArg (mk_usize 4) (mk_usize 4) (mk_usize 0) (mk_usize 1) (mk_u32 4) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 0)
      (mk_usize 0)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 1)
      (mk_usize 1)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 2)
      (mk_usize 0)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 3)
      (mk_usize 0)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 4)
      (mk_usize 0)
      ax4
  in
  s

let keccakf1600_round2_pi_rho_chi_2c (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx1: u32), (bx2: u32) =
    bx_2_ s
      (BxArg (mk_usize 4) (mk_usize 0) (mk_usize 1) (mk_usize 0) (mk_u32 18) <: t_BxArg)
      (BxArg (mk_usize 1) (mk_usize 1) (mk_usize 1) (mk_usize 0) (mk_u32 5) <: t_BxArg)
  in
  let (bx3: u32), (bx4: u32), (bx0: u32) =
    bx_3_ s
      (BxArg (mk_usize 3) (mk_usize 2) (mk_usize 1) (mk_usize 1) (mk_u32 8) <: t_BxArg)
      (BxArg (mk_usize 0) (mk_usize 3) (mk_usize 1) (mk_usize 0) (mk_u32 28) <: t_BxArg)
      (BxArg (mk_usize 2) (mk_usize 4) (mk_usize 0) (mk_usize 1) (mk_u32 14) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 0)
      (mk_usize 1)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 1)
      (mk_usize 1)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 2)
      (mk_usize 1)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 3)
      (mk_usize 1)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 4)
      (mk_usize 0)
      ax4
  in
  s

let keccakf1600_round2_pi_rho_chi_2d (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx1: u32), (bx2: u32) =
    bx_2_ s
      (BxArg (mk_usize 4) (mk_usize 0) (mk_usize 0) (mk_usize 1) (mk_u32 18) <: t_BxArg)
      (BxArg (mk_usize 1) (mk_usize 1) (mk_usize 0) (mk_usize 1) (mk_u32 5) <: t_BxArg)
  in
  let (bx3: u32), (bx4: u32), (bx0: u32) =
    bx_3_ s
      (BxArg (mk_usize 3) (mk_usize 2) (mk_usize 0) (mk_usize 0) (mk_u32 7) <: t_BxArg)
      (BxArg (mk_usize 0) (mk_usize 3) (mk_usize 0) (mk_usize 1) (mk_u32 28) <: t_BxArg)
      (BxArg (mk_usize 2) (mk_usize 4) (mk_usize 1) (mk_usize 0) (mk_u32 13) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 0)
      (mk_usize 0)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 1)
      (mk_usize 0)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 2)
      (mk_usize 0)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 3)
      (mk_usize 0)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 4)
      (mk_usize 1)
      ax4
  in
  s

let keccakf1600_round2_pi_rho_chi_2e (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx0: u32), (bx1: u32), (bx2: u32) =
    bx_3_ s
      (BxArg (mk_usize 1) (mk_usize 2) (mk_usize 1) (mk_usize 0) (mk_u32 31) <: t_BxArg)
      (BxArg (mk_usize 3) (mk_usize 3) (mk_usize 0) (mk_usize 1) (mk_u32 28) <: t_BxArg)
      (BxArg (mk_usize 0) (mk_usize 4) (mk_usize 0) (mk_usize 1) (mk_u32 20) <: t_BxArg)
  in
  let (bx3: u32), (bx4: u32) =
    bx_2_ s
      (BxArg (mk_usize 2) (mk_usize 0) (mk_usize 0) (mk_usize 1) (mk_u32 21) <: t_BxArg)
      (BxArg (mk_usize 4) (mk_usize 1) (mk_usize 0) (mk_usize 0) (mk_u32 1) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 0)
      (mk_usize 0)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 1)
      (mk_usize 0)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 2)
      (mk_usize 1)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 3)
      (mk_usize 0)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 4)
      (mk_usize 0)
      ax4
  in
  s

let keccakf1600_round2_pi_rho_chi_2f (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx0: u32), (bx1: u32), (bx2: u32) =
    bx_3_ s
      (BxArg (mk_usize 1) (mk_usize 2) (mk_usize 0) (mk_usize 1) (mk_u32 31) <: t_BxArg)
      (BxArg (mk_usize 3) (mk_usize 3) (mk_usize 1) (mk_usize 0) (mk_u32 27) <: t_BxArg)
      (BxArg (mk_usize 0) (mk_usize 4) (mk_usize 1) (mk_usize 0) (mk_u32 19) <: t_BxArg)
  in
  let (bx3: u32), (bx4: u32) =
    bx_2_ s
      (BxArg (mk_usize 2) (mk_usize 0) (mk_usize 1) (mk_usize 0) (mk_u32 20) <: t_BxArg)
      (BxArg (mk_usize 4) (mk_usize 1) (mk_usize 1) (mk_usize 1) (mk_u32 1) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 0)
      (mk_usize 1)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 1)
      (mk_usize 1)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 2)
      (mk_usize 0)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 3)
      (mk_usize 1)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 4)
      (mk_usize 1)
      ax4
  in
  s

let keccakf1600_round2_pi_rho_chi_2_ (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round2_pi_rho_chi_2a s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round2_pi_rho_chi_2b s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round2_pi_rho_chi_2c s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round2_pi_rho_chi_2d s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round2_pi_rho_chi_2e s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round2_pi_rho_chi_2f s in
  s

let keccakf1600_round3_theta_c_x0_z0 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 0) (mk_usize 0)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 0) (mk_usize 0)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 0) (mk_usize 1)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 0) (mk_usize 1)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 0) (mk_usize 0)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 0)
      (mk_usize 0)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round3_theta_c_x0_z1 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 0) (mk_usize 1)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 0) (mk_usize 1)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 0) (mk_usize 0)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 0) (mk_usize 0)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 0) (mk_usize 1)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 0)
      (mk_usize 1)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round3_theta_c_x1_z0 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 1) (mk_usize 1)
  in
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 1) (mk_usize 0)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 1) (mk_usize 0)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 1) (mk_usize 1)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 1) (mk_usize 0)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 1)
      (mk_usize 0)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round3_theta_c_x1_z1 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 1) (mk_usize 0)
  in
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 1) (mk_usize 1)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 1) (mk_usize 1)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 1) (mk_usize 0)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 1) (mk_usize 1)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 1)
      (mk_usize 1)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round3_theta_c_x2_z0 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 2) (mk_usize 0)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 2) (mk_usize 0)
  in
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 2) (mk_usize 1)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 2) (mk_usize 1)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 2) (mk_usize 1)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 2)
      (mk_usize 0)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round3_theta_c_x2_z1 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 2) (mk_usize 1)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 2) (mk_usize 1)
  in
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 2) (mk_usize 0)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 2) (mk_usize 0)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 2) (mk_usize 0)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 2)
      (mk_usize 1)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round3_theta_c_x3_z0 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 3) (mk_usize 0)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 3) (mk_usize 1)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 3) (mk_usize 1)
  in
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 3) (mk_usize 1)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 3) (mk_usize 0)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 3)
      (mk_usize 0)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round3_theta_c_x3_z1 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 3) (mk_usize 1)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 3) (mk_usize 0)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 3) (mk_usize 0)
  in
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 3) (mk_usize 0)
  in
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 3) (mk_usize 1)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 3)
      (mk_usize 1)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round3_theta_c_x4_z0 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 4) (mk_usize 1)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 4) (mk_usize 0)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 4) (mk_usize 1)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 4) (mk_usize 0)
  in
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 4) (mk_usize 0)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 4)
      (mk_usize 0)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round3_theta_c_x4_z1 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let ax_3_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 3) (mk_usize 4) (mk_usize 0)
  in
  let ax_1_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 1) (mk_usize 4) (mk_usize 1)
  in
  let ax_4_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 4) (mk_usize 4) (mk_usize 0)
  in
  let ax_2_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 2) (mk_usize 4) (mk_usize 1)
  in
  let ax_0_:u32 =
    Libcrux_iot_sha3.State.impl_KeccakState__get_with_zeta s (mk_usize 0) (mk_usize 4) (mk_usize 1)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_lane_value s
      (mk_usize 4)
      (mk_usize 1)
      ((((ax_0_ ^. ax_1_ <: u32) ^. ax_2_ <: u32) ^. ax_3_ <: u32) ^. ax_4_ <: u32)
  in
  s

let keccakf1600_round3_theta_d_x0 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let c_x4_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 4 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let c_x1_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 1 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x4_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 4 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x1_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 1 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 0)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 0 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 0 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 0)
              (c_x4_zeta0 ^. (Core_models.Num.impl_u32__rotate_left c_x1_zeta1 (mk_u32 1) <: u32)
                <:
                u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 0)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 0 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 0 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 1)
              (c_x4_zeta1 ^. c_x1_zeta0 <: u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  s

let keccakf1600_round3_theta_d_x1 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let c_x0_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 0 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let c_x2_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 2 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x0_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 0 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x2_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 2 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 1)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 1 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 1 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 0)
              (c_x0_zeta0 ^. (Core_models.Num.impl_u32__rotate_left c_x2_zeta1 (mk_u32 1) <: u32)
                <:
                u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 1)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 1 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 1 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 1)
              (c_x0_zeta1 ^. c_x2_zeta0 <: u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  s

let keccakf1600_round3_theta_d_x2 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let c_x1_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 1 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let c_x3_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 3 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x1_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 1 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x3_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 3 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 2)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 2 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 2 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 0)
              (c_x1_zeta0 ^. (Core_models.Num.impl_u32__rotate_left c_x3_zeta1 (mk_u32 1) <: u32)
                <:
                u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 2)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 2 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 2 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 1)
              (c_x1_zeta1 ^. c_x3_zeta0 <: u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  s

let keccakf1600_round3_theta_d_x3 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let c_x2_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 2 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let c_x4_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 4 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x2_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 2 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x4_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 4 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 3)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 3 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 3 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 0)
              (c_x2_zeta0 ^. (Core_models.Num.impl_u32__rotate_left c_x4_zeta1 (mk_u32 1) <: u32)
                <:
                u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 3)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 3 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 3 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 1)
              (c_x2_zeta1 ^. c_x4_zeta0 <: u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  s

let keccakf1600_round3_theta_d_x4 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let c_x3_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 3 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let c_x0_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 0 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x3_zeta1:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 3 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 1 ]
  in
  let c_x0_zeta0:u32 =
    (s.Libcrux_iot_sha3.State.f_c.[ mk_usize 0 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ mk_usize 0 ]
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 4)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 4 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 4 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 0)
              (c_x3_zeta0 ^. (Core_models.Num.impl_u32__rotate_left c_x0_zeta1 (mk_u32 1) <: u32)
                <:
                u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    {
      s with
      Libcrux_iot_sha3.State.f_d
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s.Libcrux_iot_sha3.State.f_d
        (mk_usize 4)
        ({
            (s.Libcrux_iot_sha3.State.f_d.[ mk_usize 4 ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (s
                  .Libcrux_iot_sha3.State.f_d.[ mk_usize 4 ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              (mk_usize 1)
              (c_x3_zeta1 ^. c_x0_zeta0 <: u32)
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    Libcrux_iot_sha3.State.t_KeccakState
  in
  s

let keccakf1600_round3_theta_d (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round3_theta_d_x0 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round3_theta_d_x1 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round3_theta_d_x2 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round3_theta_d_x3 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round3_theta_d_x4 s in
  s

let keccakf1600_round3_theta (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round3_theta_c_x0_z0 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round3_theta_c_x0_z1 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round3_theta_c_x1_z0 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round3_theta_c_x1_z1 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round3_theta_c_x2_z0 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round3_theta_c_x2_z1 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round3_theta_c_x3_z0 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round3_theta_c_x3_z1 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round3_theta_c_x4_z0 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round3_theta_c_x4_z1 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round3_theta_d s in
  s

let keccakf1600_round3_pi_rho_chi_1a (v_BASE_ROUND: usize) (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Prims.Pure Libcrux_iot_sha3.State.t_KeccakState
      (requires v_BASE_ROUND <. mk_usize 252)
      (fun _ -> Prims.l_True) =
  let (bx0: u32), (bx1: u32) =
    bx_2_ s
      (BxArg (mk_usize 0) (mk_usize 0) (mk_usize 0) (mk_usize 0) (mk_u32 0) <: t_BxArg)
      (BxArg (mk_usize 0) (mk_usize 1) (mk_usize 0) (mk_usize 0) (mk_u32 22) <: t_BxArg)
  in
  let (bx2: u32), (bx3: u32), (bx4: u32) =
    bx_3_ s
      (BxArg (mk_usize 0) (mk_usize 2) (mk_usize 0) (mk_usize 1) (mk_u32 22) <: t_BxArg)
      (BxArg (mk_usize 0) (mk_usize 3) (mk_usize 0) (mk_usize 1) (mk_u32 11) <: t_BxArg)
      (BxArg (mk_usize 0) (mk_usize 4) (mk_usize 0) (mk_usize 0) (mk_u32 7) <: t_BxArg)
  in
  let ax0:u32 =
    (bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) <: u32) ^.
    (v_RC_INTERLEAVED_0_.[ v_BASE_ROUND +! mk_usize 3 <: usize ] <: u32)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 0)
      (mk_usize 0)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 1)
      (mk_usize 0)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 2)
      (mk_usize 0)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 3)
      (mk_usize 0)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 4)
      (mk_usize 0)
      ax4
  in
  s

let keccakf1600_round3_pi_rho_chi_1b (v_BASE_ROUND: usize) (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Prims.Pure Libcrux_iot_sha3.State.t_KeccakState
      (requires v_BASE_ROUND <. mk_usize 252)
      (fun _ -> Prims.l_True) =
  let (bx0: u32), (bx1: u32) =
    bx_2_ s
      (BxArg (mk_usize 0) (mk_usize 0) (mk_usize 1) (mk_usize 1) (mk_u32 0) <: t_BxArg)
      (BxArg (mk_usize 0) (mk_usize 1) (mk_usize 1) (mk_usize 1) (mk_u32 22) <: t_BxArg)
  in
  let (bx2: u32), (bx3: u32), (bx4: u32) =
    bx_3_ s
      (BxArg (mk_usize 0) (mk_usize 2) (mk_usize 1) (mk_usize 0) (mk_u32 21) <: t_BxArg)
      (BxArg (mk_usize 0) (mk_usize 3) (mk_usize 1) (mk_usize 0) (mk_u32 10) <: t_BxArg)
      (BxArg (mk_usize 0) (mk_usize 4) (mk_usize 1) (mk_usize 1) (mk_u32 7) <: t_BxArg)
  in
  let ax0:u32 =
    (bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) <: u32) ^.
    (v_RC_INTERLEAVED_1_.[ v_BASE_ROUND +! mk_usize 3 <: usize ] <: u32)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 0)
      (mk_usize 1)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 1)
      (mk_usize 1)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 2)
      (mk_usize 1)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 3)
      (mk_usize 1)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 0)
      (mk_usize 4)
      (mk_usize 1)
      ax4
  in
  s

let keccakf1600_round3_pi_rho_chi_1c (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx4: u32), (bx0: u32), (bx1: u32) =
    bx_3_ s
      (BxArg (mk_usize 1) (mk_usize 2) (mk_usize 0) (mk_usize 1) (mk_u32 31) <: t_BxArg)
      (BxArg (mk_usize 1) (mk_usize 3) (mk_usize 0) (mk_usize 0) (mk_u32 14) <: t_BxArg)
      (BxArg (mk_usize 1) (mk_usize 4) (mk_usize 0) (mk_usize 0) (mk_u32 10) <: t_BxArg)
  in
  let (bx2: u32), (bx3: u32) =
    bx_2_ s
      (BxArg (mk_usize 1) (mk_usize 0) (mk_usize 0) (mk_usize 1) (mk_u32 2) <: t_BxArg)
      (BxArg (mk_usize 1) (mk_usize 1) (mk_usize 0) (mk_usize 1) (mk_u32 23) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 0)
      (mk_usize 0)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 1)
      (mk_usize 0)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 2)
      (mk_usize 0)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 3)
      (mk_usize 0)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 4)
      (mk_usize 0)
      ax4
  in
  s

let keccakf1600_round3_pi_rho_chi_1d (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx4: u32), (bx0: u32), (bx1: u32) =
    bx_3_ s
      (BxArg (mk_usize 1) (mk_usize 2) (mk_usize 1) (mk_usize 0) (mk_u32 30) <: t_BxArg)
      (BxArg (mk_usize 1) (mk_usize 3) (mk_usize 1) (mk_usize 1) (mk_u32 14) <: t_BxArg)
      (BxArg (mk_usize 1) (mk_usize 4) (mk_usize 1) (mk_usize 1) (mk_u32 10) <: t_BxArg)
  in
  let (bx2: u32), (bx3: u32) =
    bx_2_ s
      (BxArg (mk_usize 1) (mk_usize 0) (mk_usize 1) (mk_usize 0) (mk_u32 1) <: t_BxArg)
      (BxArg (mk_usize 1) (mk_usize 1) (mk_usize 1) (mk_usize 0) (mk_u32 22) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 0)
      (mk_usize 1)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 1)
      (mk_usize 1)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 2)
      (mk_usize 1)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 3)
      (mk_usize 1)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 1)
      (mk_usize 4)
      (mk_usize 1)
      ax4
  in
  s

let keccakf1600_round3_pi_rho_chi_1_ (v_BASE_ROUND: usize) (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Prims.Pure Libcrux_iot_sha3.State.t_KeccakState
      (requires v_BASE_ROUND <. mk_usize 252)
      (fun _ -> Prims.l_True) =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round3_pi_rho_chi_1a v_BASE_ROUND s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round3_pi_rho_chi_1b v_BASE_ROUND s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round3_pi_rho_chi_1c s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round3_pi_rho_chi_1d s in
  s

let keccakf1600_round3_pi_rho_chi_2a (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx4: u32), (bx0: u32) =
    bx_2_ s
      (BxArg (mk_usize 2) (mk_usize 0) (mk_usize 0) (mk_usize 0) (mk_u32 9) <: t_BxArg)
      (BxArg (mk_usize 2) (mk_usize 1) (mk_usize 0) (mk_usize 1) (mk_u32 1) <: t_BxArg)
  in
  let (bx1: u32), (bx2: u32), (bx3: u32) =
    bx_3_ s
      (BxArg (mk_usize 2) (mk_usize 2) (mk_usize 0) (mk_usize 0) (mk_u32 3) <: t_BxArg)
      (BxArg (mk_usize 2) (mk_usize 3) (mk_usize 0) (mk_usize 1) (mk_u32 13) <: t_BxArg)
      (BxArg (mk_usize 2) (mk_usize 4) (mk_usize 0) (mk_usize 0) (mk_u32 4) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 0)
      (mk_usize 0)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 1)
      (mk_usize 0)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 2)
      (mk_usize 0)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 3)
      (mk_usize 0)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 4)
      (mk_usize 0)
      ax4
  in
  s

let keccakf1600_round3_pi_rho_chi_2b (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx4: u32), (bx0: u32) =
    bx_2_ s
      (BxArg (mk_usize 2) (mk_usize 0) (mk_usize 1) (mk_usize 1) (mk_u32 9) <: t_BxArg)
      (BxArg (mk_usize 2) (mk_usize 1) (mk_usize 1) (mk_usize 0) (mk_u32 0) <: t_BxArg)
  in
  let (bx1: u32), (bx2: u32), (bx3: u32) =
    bx_3_ s
      (BxArg (mk_usize 2) (mk_usize 2) (mk_usize 1) (mk_usize 1) (mk_u32 3) <: t_BxArg)
      (BxArg (mk_usize 2) (mk_usize 3) (mk_usize 1) (mk_usize 0) (mk_u32 12) <: t_BxArg)
      (BxArg (mk_usize 2) (mk_usize 4) (mk_usize 1) (mk_usize 1) (mk_u32 4) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 0)
      (mk_usize 1)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 1)
      (mk_usize 1)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 2)
      (mk_usize 1)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 3)
      (mk_usize 1)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 2)
      (mk_usize 4)
      (mk_usize 1)
      ax4
  in
  s

let keccakf1600_round3_pi_rho_chi_2c (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx1: u32), (bx2: u32) =
    bx_2_ s
      (BxArg (mk_usize 3) (mk_usize 0) (mk_usize 0) (mk_usize 0) (mk_u32 18) <: t_BxArg)
      (BxArg (mk_usize 3) (mk_usize 1) (mk_usize 0) (mk_usize 0) (mk_u32 5) <: t_BxArg)
  in
  let (bx3: u32), (bx4: u32), (bx0: u32) =
    bx_3_ s
      (BxArg (mk_usize 3) (mk_usize 2) (mk_usize 0) (mk_usize 1) (mk_u32 8) <: t_BxArg)
      (BxArg (mk_usize 3) (mk_usize 3) (mk_usize 0) (mk_usize 0) (mk_u32 28) <: t_BxArg)
      (BxArg (mk_usize 3) (mk_usize 4) (mk_usize 0) (mk_usize 1) (mk_u32 14) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 0)
      (mk_usize 0)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 1)
      (mk_usize 0)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 2)
      (mk_usize 0)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 3)
      (mk_usize 0)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 4)
      (mk_usize 0)
      ax4
  in
  s

let keccakf1600_round3_pi_rho_chi_2d (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx1: u32), (bx2: u32) =
    bx_2_ s
      (BxArg (mk_usize 3) (mk_usize 0) (mk_usize 1) (mk_usize 1) (mk_u32 18) <: t_BxArg)
      (BxArg (mk_usize 3) (mk_usize 1) (mk_usize 1) (mk_usize 1) (mk_u32 5) <: t_BxArg)
  in
  let (bx3: u32), (bx4: u32), (bx0: u32) =
    bx_3_ s
      (BxArg (mk_usize 3) (mk_usize 2) (mk_usize 1) (mk_usize 0) (mk_u32 7) <: t_BxArg)
      (BxArg (mk_usize 3) (mk_usize 3) (mk_usize 1) (mk_usize 1) (mk_u32 28) <: t_BxArg)
      (BxArg (mk_usize 3) (mk_usize 4) (mk_usize 1) (mk_usize 0) (mk_u32 13) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 0)
      (mk_usize 1)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 1)
      (mk_usize 1)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 2)
      (mk_usize 1)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 3)
      (mk_usize 1)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 3)
      (mk_usize 4)
      (mk_usize 1)
      ax4
  in
  s

let keccakf1600_round3_pi_rho_chi_2e (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx0: u32), (bx1: u32), (bx2: u32) =
    bx_3_ s
      (BxArg (mk_usize 4) (mk_usize 2) (mk_usize 0) (mk_usize 0) (mk_u32 31) <: t_BxArg)
      (BxArg (mk_usize 4) (mk_usize 3) (mk_usize 0) (mk_usize 1) (mk_u32 28) <: t_BxArg)
      (BxArg (mk_usize 4) (mk_usize 4) (mk_usize 0) (mk_usize 1) (mk_u32 20) <: t_BxArg)
  in
  let (bx3: u32), (bx4: u32) =
    bx_2_ s
      (BxArg (mk_usize 4) (mk_usize 0) (mk_usize 0) (mk_usize 1) (mk_u32 21) <: t_BxArg)
      (BxArg (mk_usize 4) (mk_usize 1) (mk_usize 0) (mk_usize 0) (mk_u32 1) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 0)
      (mk_usize 0)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 1)
      (mk_usize 0)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 2)
      (mk_usize 0)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 3)
      (mk_usize 0)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 4)
      (mk_usize 0)
      ax4
  in
  s

let keccakf1600_round3_pi_rho_chi_2f (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let (bx0: u32), (bx1: u32), (bx2: u32) =
    bx_3_ s
      (BxArg (mk_usize 4) (mk_usize 2) (mk_usize 1) (mk_usize 1) (mk_u32 31) <: t_BxArg)
      (BxArg (mk_usize 4) (mk_usize 3) (mk_usize 1) (mk_usize 0) (mk_u32 27) <: t_BxArg)
      (BxArg (mk_usize 4) (mk_usize 4) (mk_usize 1) (mk_usize 0) (mk_u32 19) <: t_BxArg)
  in
  let (bx3: u32), (bx4: u32) =
    bx_2_ s
      (BxArg (mk_usize 4) (mk_usize 0) (mk_usize 1) (mk_usize 0) (mk_u32 20) <: t_BxArg)
      (BxArg (mk_usize 4) (mk_usize 1) (mk_usize 1) (mk_usize 1) (mk_u32 1) <: t_BxArg)
  in
  let ax0:u32 = bx0 ^. ((~.bx1 <: u32) &. bx2 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 0)
      (mk_usize 1)
      ax0
  in
  let ax1:u32 = bx1 ^. ((~.bx2 <: u32) &. bx3 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 1)
      (mk_usize 1)
      ax1
  in
  let ax2:u32 = bx2 ^. ((~.bx3 <: u32) &. bx4 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 2)
      (mk_usize 1)
      ax2
  in
  let ax3:u32 = bx3 ^. ((~.bx4 <: u32) &. bx0 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 3)
      (mk_usize 1)
      ax3
  in
  let ax4:u32 = bx4 ^. ((~.bx0 <: u32) &. bx1 <: u32) in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__set_with_zeta s
      (mk_usize 4)
      (mk_usize 4)
      (mk_usize 1)
      ax4
  in
  s

let keccakf1600_round3_pi_rho_chi_2_ (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round3_pi_rho_chi_2a s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round3_pi_rho_chi_2b s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round3_pi_rho_chi_2c s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round3_pi_rho_chi_2d s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round3_pi_rho_chi_2e s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round3_pi_rho_chi_2f s in
  s

#push-options "--z3rlimit 60"

let keccakf1600_round0 (v_BASE_ROUND: usize) (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Prims.Pure Libcrux_iot_sha3.State.t_KeccakState
      (requires v_BASE_ROUND <. mk_usize 255)
      (fun _ -> Prims.l_True) =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round0_theta s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round0_pi_rho_chi_1_ v_BASE_ROUND s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round0_pi_rho_chi_2_ s in
  s

#pop-options

let keccakf1600_round1 (v_BASE_ROUND: usize) (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Prims.Pure Libcrux_iot_sha3.State.t_KeccakState
      (requires v_BASE_ROUND <. mk_usize 254)
      (fun _ -> Prims.l_True) =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round1_theta s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round1_pi_rho_chi_1_ v_BASE_ROUND s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round1_pi_rho_chi_2_ s in
  s

let keccakf1600_round2 (v_BASE_ROUND: usize) (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Prims.Pure Libcrux_iot_sha3.State.t_KeccakState
      (requires v_BASE_ROUND <. mk_usize 253)
      (fun _ -> Prims.l_True) =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round2_theta s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round2_pi_rho_chi_1_ v_BASE_ROUND s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round2_pi_rho_chi_2_ s in
  s

#push-options "--z3rlimit 60"

let keccakf1600_round3 (v_BASE_ROUND: usize) (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Prims.Pure Libcrux_iot_sha3.State.t_KeccakState
      (requires v_BASE_ROUND <. mk_usize 252)
      (fun _ -> Prims.l_True) =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round3_theta s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round3_pi_rho_chi_1_ v_BASE_ROUND s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round3_pi_rho_chi_2_ s in
  s

#pop-options

#push-options "--z3rlimit 60"

let keccakf1600_4rounds (v_BASE_ROUND: usize) (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Prims.Pure Libcrux_iot_sha3.State.t_KeccakState
      (requires v_BASE_ROUND <. mk_usize 21)
      (fun _ -> Prims.l_True) =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round0 v_BASE_ROUND s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round1 v_BASE_ROUND s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round2 v_BASE_ROUND s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_round3 v_BASE_ROUND s in
  s

#pop-options

let keccakf1600_4rounds0 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_4rounds (mk_usize 0) s in
  s

let keccakf1600_4rounds4 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_4rounds (mk_usize 4) s in
  s

let keccakf1600_4rounds8 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_4rounds (mk_usize 8) s in
  s

let keccakf1600_4rounds12 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_4rounds (mk_usize 12) s in
  s

let keccakf1600_4rounds16 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_4rounds (mk_usize 16) s in
  s

let keccakf1600_4rounds20 (s: Libcrux_iot_sha3.State.t_KeccakState)
    : Libcrux_iot_sha3.State.t_KeccakState =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_4rounds (mk_usize 20) s in
  s

#push-options "--z3rlimit 60"

let keccakf1600 (s: Libcrux_iot_sha3.State.t_KeccakState) : Libcrux_iot_sha3.State.t_KeccakState =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_4rounds0 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_4rounds4 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_4rounds8 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_4rounds12 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_4rounds16 s in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600_4rounds20 s in
  s

#pop-options

let squeeze_update
      (v_RATE: usize)
      (state: Libcrux_iot_sha3.State.t_KeccakState)
      (out: t_Slice u8)
      (offset: usize)
    : Prims.Pure (Libcrux_iot_sha3.State.t_KeccakState & t_Slice u8)
      (requires
        v_RATE >. mk_usize 0 && (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 &&
        v_RATE <=. mk_usize 168 &&
        ((Rust_primitives.Hax.Int.from_machine offset <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine v_RATE <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine (Core_models.Slice.impl__len #u8 out <: usize)
          <:
          Hax_lib.Int.t_Int))
      (ensures
        fun temp_0_ ->
          let (state_future: Libcrux_iot_sha3.State.t_KeccakState), (out_future: t_Slice u8) =
            temp_0_
          in
          (Core_models.Slice.impl__len #u8 out_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out <: usize)) =
  let state:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600 state in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
      ({
          Core_models.Ops.Range.f_start = offset;
          Core_models.Ops.Range.f_end = offset +! v_RATE <: usize
        }
        <:
        Core_models.Ops.Range.t_Range usize)
      (Libcrux_iot_sha3.State.impl_KeccakState__store v_RATE
          state
          (out.[ {
                Core_models.Ops.Range.f_start = offset;
                Core_models.Ops.Range.f_end = offset +! v_RATE <: usize
              }
              <:
              Core_models.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  state, out <: (Libcrux_iot_sha3.State.t_KeccakState & t_Slice u8)

#push-options "--z3rlimit 100 --split_queries always"

let e_squeeze (v_RATE: usize) (state: t_KeccakXofState v_RATE) (out: t_Slice u8)
    : Prims.Pure (t_KeccakXofState v_RATE & t_Slice u8)
      (requires
        v_RATE >. mk_usize 0 && (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 &&
        v_RATE <=. mk_usize 168)
      (fun _ -> Prims.l_True) =
  let state:t_KeccakXofState v_RATE =
    if state.f_sponge
    then
      let state:t_KeccakXofState v_RATE =
        { state with f_inner = keccakf1600 state.f_inner } <: t_KeccakXofState v_RATE
      in
      state
    else state
  in
  let out_len:usize = Core_models.Slice.impl__len #u8 out in
  let blocks:usize = out_len /! v_RATE in
  let last:usize = out_len -! (out_len %! v_RATE <: usize) in
  let mid:usize = if v_RATE >=. out_len then out_len else v_RATE in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_to out
      ({ Core_models.Ops.Range.f_end = mid } <: Core_models.Ops.Range.t_RangeTo usize)
      (Libcrux_iot_sha3.State.impl_KeccakState__store v_RATE
          state.f_inner
          (out.[ { Core_models.Ops.Range.f_end = mid } <: Core_models.Ops.Range.t_RangeTo usize ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let offset:usize = mid in
  let (offset: usize), (out: t_Slice u8), (state: t_KeccakXofState v_RATE) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 1)
      blocks
      (fun temp_0_ e_k ->
          let (offset: usize), (out: t_Slice u8), (state: t_KeccakXofState v_RATE) = temp_0_ in
          let e_k:usize = e_k in
          ((Core_models.Slice.impl__len #u8 out <: usize) =. out_len <: bool) &&
          ((Rust_primitives.Hax.Int.from_machine offset <: Hax_lib.Int.t_Int) =
            ((Rust_primitives.Hax.Int.from_machine e_k <: Hax_lib.Int.t_Int) *
              (Rust_primitives.Hax.Int.from_machine v_RATE <: Hax_lib.Int.t_Int)
              <:
              Hax_lib.Int.t_Int)
            <:
            bool) &&
          ((offset -! v_RATE <: usize) <=. (Core_models.Slice.impl__len #u8 out <: usize) <: bool))
      (offset, out, state <: (usize & t_Slice u8 & t_KeccakXofState v_RATE))
      (fun temp_0_ e_k ->
          let (offset: usize), (out: t_Slice u8), (state: t_KeccakXofState v_RATE) = temp_0_ in
          let e_k:usize = e_k in
          let (tmp0: Libcrux_iot_sha3.State.t_KeccakState), (tmp1: t_Slice u8) =
            squeeze_update v_RATE state.f_inner out offset
          in
          let state:t_KeccakXofState v_RATE =
            { state with f_inner = tmp0 } <: t_KeccakXofState v_RATE
          in
          let out:t_Slice u8 = tmp1 in
          let _:Prims.unit = () in
          let offset:usize = offset +! v_RATE in
          offset, out, state <: (usize & t_Slice u8 & t_KeccakXofState v_RATE))
  in
  let (out: t_Slice u8), (state: t_KeccakXofState v_RATE) =
    if last >. mk_usize 0 && last <. out_len
    then
      let _:Prims.unit =
        if true
        then
          let _:Prims.unit =
            match last, offset <: (usize & usize) with
            | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
          in
          ()
      in
      let state:t_KeccakXofState v_RATE =
        { state with f_inner = keccakf1600 state.f_inner } <: t_KeccakXofState v_RATE
      in
      let out:t_Slice u8 =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from out
          ({ Core_models.Ops.Range.f_start = offset } <: Core_models.Ops.Range.t_RangeFrom usize)
          (Libcrux_iot_sha3.State.impl_KeccakState__store v_RATE
              state.f_inner
              (out.[ { Core_models.Ops.Range.f_start = offset }
                  <:
                  Core_models.Ops.Range.t_RangeFrom usize ]
                <:
                t_Slice u8)
            <:
            t_Slice u8)
      in
      out, state <: (t_Slice u8 & t_KeccakXofState v_RATE)
    else out, state <: (t_Slice u8 & t_KeccakXofState v_RATE)
  in
  let state:t_KeccakXofState v_RATE = { state with f_sponge = true } <: t_KeccakXofState v_RATE in
  state, out <: (t_KeccakXofState v_RATE & t_Slice u8)

#pop-options

/// Squeeze `N` x `LEN` bytes.
let impl__squeeze (v_RATE: usize) (self: t_KeccakXofState v_RATE) (out: t_Slice u8)
    : Prims.Pure (t_KeccakXofState v_RATE & t_Slice u8)
      (requires
        v_RATE >. mk_usize 0 && (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 &&
        v_RATE <=. mk_usize 168)
      (ensures
        fun temp_0_ ->
          let (self_e_future: t_KeccakXofState v_RATE), (out_future: t_Slice u8) = temp_0_ in
          (Core_models.Slice.impl__len #u8 out_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out <: usize)) =
  let (tmp0: t_KeccakXofState v_RATE), (tmp1: t_Slice u8) = e_squeeze v_RATE self out in
  let self:t_KeccakXofState v_RATE = tmp0 in
  let out:t_Slice u8 = tmp1 in
  let _:Prims.unit = () in
  self, out <: (t_KeccakXofState v_RATE & t_Slice u8)

#push-options "--z3rlimit 100"

let e_absorb_full (v_RATE: usize) (state: t_KeccakXofState v_RATE) (inputs: t_Slice u8)
    : Prims.Pure (t_KeccakXofState v_RATE & usize)
      (requires
        v_RATE >. mk_usize 0 && (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 &&
        v_RATE <=. mk_usize 168 &&
        state.f_buf_len <. v_RATE &&
        ((Rust_primitives.Hax.Int.from_machine (Core_models.Slice.impl__len #u8 inputs <: usize)
            <:
            Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine state.f_buf_len <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_usize__MAX <: Hax_lib.Int.t_Int))
      (ensures
        fun temp_0_ ->
          let (state_future: t_KeccakXofState v_RATE), (remainder: usize) = temp_0_ in
          remainder <. v_RATE && remainder <=. (Core_models.Slice.impl__len #u8 inputs <: usize) &&
          state_future.f_buf_len <=. v_RATE &&
          ((Rust_primitives.Hax.Int.from_machine state_future.f_buf_len <: Hax_lib.Int.t_Int) +
            (Rust_primitives.Hax.Int.from_machine remainder <: Hax_lib.Int.t_Int)
            <:
            Hax_lib.Int.t_Int) <
          (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_usize__MAX <: Hax_lib.Int.t_Int
          )) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit = Hax_lib.v_assert (state.f_buf_len <. v_RATE <: bool) in
      ()
  in
  let (tmp0: t_KeccakXofState v_RATE), (out: usize) = impl__fill_buffer v_RATE state inputs in
  let state:t_KeccakXofState v_RATE = tmp0 in
  let input_consumed:usize = out in
  let state:t_KeccakXofState v_RATE =
    if input_consumed >. mk_usize 0
    then
      let state:t_KeccakXofState v_RATE =
        {
          state with
          f_inner
          =
          Libcrux_iot_sha3.State.impl_KeccakState__load_block v_RATE
            state.f_inner
            (state.f_buf <: t_Slice u8)
            (mk_usize 0)
        }
        <:
        t_KeccakXofState v_RATE
      in
      let state:t_KeccakXofState v_RATE =
        { state with f_inner = keccakf1600 state.f_inner } <: t_KeccakXofState v_RATE
      in
      let state:t_KeccakXofState v_RATE =
        { state with f_buf_len = mk_usize 0 } <: t_KeccakXofState v_RATE
      in
      state
    else state
  in
  let input_to_consume:usize =
    (Core_models.Slice.impl__len #u8 inputs <: usize) -! input_consumed
  in
  let num_blocks:usize = input_to_consume /! v_RATE in
  let remainder:usize = input_to_consume %! v_RATE in
  let e_buf_len:usize = state.f_buf_len in
  let state:t_KeccakXofState v_RATE =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      num_blocks
      (fun state e_i ->
          let state:t_KeccakXofState v_RATE = state in
          let e_i:usize = e_i in
          state.f_buf_len =. e_buf_len <: bool)
      state
      (fun state i ->
          let state:t_KeccakXofState v_RATE = state in
          let i:usize = i in
          let state:t_KeccakXofState v_RATE =
            {
              state with
              f_inner
              =
              Libcrux_iot_sha3.State.impl_KeccakState__load_block v_RATE
                state.f_inner
                inputs
                (input_consumed +! (i *! v_RATE <: usize) <: usize)
            }
            <:
            t_KeccakXofState v_RATE
          in
          let state:t_KeccakXofState v_RATE =
            { state with f_inner = keccakf1600 state.f_inner } <: t_KeccakXofState v_RATE
          in
          state)
  in
  let hax_temp_output:usize = remainder in
  state, hax_temp_output <: (t_KeccakXofState v_RATE & usize)

#pop-options

let impl__absorb_full (v_RATE: usize) (self: t_KeccakXofState v_RATE) (inputs: t_Slice u8)
    : Prims.Pure (t_KeccakXofState v_RATE & usize)
      (requires
        v_RATE >. mk_usize 0 && (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 &&
        v_RATE <=. mk_usize 168 &&
        self.f_buf_len <. v_RATE &&
        ((Rust_primitives.Hax.Int.from_machine (Core_models.Slice.impl__len #u8 inputs <: usize)
            <:
            Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine self.f_buf_len <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_usize__MAX <: Hax_lib.Int.t_Int))
      (ensures
        fun temp_0_ ->
          let (self_e_future: t_KeccakXofState v_RATE), (remainder: usize) = temp_0_ in
          remainder <. v_RATE && remainder <=. (Core_models.Slice.impl__len #u8 inputs <: usize) &&
          self_e_future.f_buf_len <=. v_RATE &&
          ((Rust_primitives.Hax.Int.from_machine self_e_future.f_buf_len <: Hax_lib.Int.t_Int) +
            (Rust_primitives.Hax.Int.from_machine remainder <: Hax_lib.Int.t_Int)
            <:
            Hax_lib.Int.t_Int) <
          (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_usize__MAX <: Hax_lib.Int.t_Int
          )) =
  let (tmp0: t_KeccakXofState v_RATE), (out: usize) = e_absorb_full v_RATE self inputs in
  let self:t_KeccakXofState v_RATE = tmp0 in
  let hax_temp_output:usize = out in
  self, hax_temp_output <: (t_KeccakXofState v_RATE & usize)

/// Absorb
/// This function takes any number of bytes to absorb and buffers if it\'s not enough.
/// The function assumes that all input slices in `blocks` have the same length.
/// Only a multiple of `RATE` blocks are absorbed.
/// For the remaining bytes [`absorb_final`] needs to be called.
/// This works best with relatively small `inputs`.
let impl__absorb (v_RATE: usize) (self: t_KeccakXofState v_RATE) (inputs: t_Slice u8)
    : Prims.Pure (t_KeccakXofState v_RATE)
      (requires
        v_RATE >. mk_usize 0 && (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 &&
        v_RATE <=. mk_usize 168 &&
        self.f_buf_len <. v_RATE &&
        ((Rust_primitives.Hax.Int.from_machine (Core_models.Slice.impl__len #u8 inputs <: usize)
            <:
            Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine self.f_buf_len <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_usize__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (tmp0: t_KeccakXofState v_RATE), (out: usize) = impl__absorb_full v_RATE self inputs in
  let self:t_KeccakXofState v_RATE = tmp0 in
  let input_remainder_len:usize = out in
  let self:t_KeccakXofState v_RATE =
    if input_remainder_len >. mk_usize 0
    then
      let _:Prims.unit =
        if true
        then
          let _:Prims.unit =
            Hax_lib.v_assert ((self.f_buf_len =. mk_usize 0 <: bool) ||
                ((self.f_buf_len +! input_remainder_len <: usize) <=. v_RATE <: bool))
          in
          ()
      in
      let input_len:usize = Core_models.Slice.impl__len #u8 inputs in
      let self:t_KeccakXofState v_RATE =
        {
          self with
          f_buf
          =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_range self.f_buf
            ({
                Core_models.Ops.Range.f_start = self.f_buf_len;
                Core_models.Ops.Range.f_end = self.f_buf_len +! input_remainder_len <: usize
              }
              <:
              Core_models.Ops.Range.t_Range usize)
            (Core_models.Slice.impl__copy_from_slice #u8
                (self.f_buf.[ {
                      Core_models.Ops.Range.f_start = self.f_buf_len;
                      Core_models.Ops.Range.f_end = self.f_buf_len +! input_remainder_len <: usize
                    }
                    <:
                    Core_models.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
                (inputs.[ {
                      Core_models.Ops.Range.f_start = input_len -! input_remainder_len <: usize
                    }
                    <:
                    Core_models.Ops.Range.t_RangeFrom usize ]
                  <:
                  t_Slice u8)
              <:
              t_Slice u8)
        }
        <:
        t_KeccakXofState v_RATE
      in
      let self:t_KeccakXofState v_RATE =
        { self with f_buf_len = self.f_buf_len +! input_remainder_len } <: t_KeccakXofState v_RATE
      in
      self
    else self
  in
  self

/// Absorb a final block.
/// The `inputs` block may be empty. Everything in the `inputs` block beyond
/// `RATE` bytes is ignored.
let impl__absorb_final
      (v_RATE: usize)
      (v_DELIMITER: u8)
      (self: t_KeccakXofState v_RATE)
      (inputs: t_Slice u8)
    : Prims.Pure (t_KeccakXofState v_RATE)
      (requires
        v_RATE >. mk_usize 0 && (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 &&
        v_RATE <=. mk_usize 168 &&
        self.f_buf_len <. v_RATE &&
        ((Rust_primitives.Hax.Int.from_machine (Core_models.Slice.impl__len #u8 inputs <: usize)
            <:
            Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine self.f_buf_len <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_usize__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (tmp0: t_KeccakXofState v_RATE), (out: usize) = impl__absorb_full v_RATE self inputs in
  let self:t_KeccakXofState v_RATE = tmp0 in
  let input_remainder_len:usize = out in
  let input_len:usize = Core_models.Slice.impl__len #u8 inputs in
  let blocks:t_Array u8 (mk_usize 200) =
    Libcrux_secrets.Traits.f_classify #(t_Array u8 (mk_usize 200))
      #FStar.Tactics.Typeclasses.solve
      (Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 200) <: t_Array u8 (mk_usize 200))
  in
  let blocks:t_Array u8 (mk_usize 200) =
    if self.f_buf_len >. mk_usize 0
    then
      let blocks:t_Array u8 (mk_usize 200) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_range blocks
          ({
              Core_models.Ops.Range.f_start = mk_usize 0;
              Core_models.Ops.Range.f_end = self.f_buf_len
            }
            <:
            Core_models.Ops.Range.t_Range usize)
          (Core_models.Slice.impl__copy_from_slice #u8
              (blocks.[ {
                    Core_models.Ops.Range.f_start = mk_usize 0;
                    Core_models.Ops.Range.f_end = self.f_buf_len
                  }
                  <:
                  Core_models.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
              (self.f_buf.[ {
                    Core_models.Ops.Range.f_start = mk_usize 0;
                    Core_models.Ops.Range.f_end = self.f_buf_len
                  }
                  <:
                  Core_models.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            t_Slice u8)
      in
      blocks
    else blocks
  in
  let blocks:t_Array u8 (mk_usize 200) =
    if input_remainder_len >. mk_usize 0
    then
      let blocks:t_Array u8 (mk_usize 200) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_range blocks
          ({
              Core_models.Ops.Range.f_start = self.f_buf_len;
              Core_models.Ops.Range.f_end = self.f_buf_len +! input_remainder_len <: usize
            }
            <:
            Core_models.Ops.Range.t_Range usize)
          (Core_models.Slice.impl__copy_from_slice #u8
              (blocks.[ {
                    Core_models.Ops.Range.f_start = self.f_buf_len;
                    Core_models.Ops.Range.f_end = self.f_buf_len +! input_remainder_len <: usize
                  }
                  <:
                  Core_models.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
              (inputs.[ {
                    Core_models.Ops.Range.f_start = input_len -! input_remainder_len <: usize
                  }
                  <:
                  Core_models.Ops.Range.t_RangeFrom usize ]
                <:
                t_Slice u8)
            <:
            t_Slice u8)
      in
      blocks
    else blocks
  in
  let blocks:t_Array u8 (mk_usize 200) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize blocks
      (self.f_buf_len +! input_remainder_len <: usize)
      (Libcrux_secrets.Traits.f_classify #u8 #FStar.Tactics.Typeclasses.solve v_DELIMITER <: u8)
  in
  let blocks:t_Array u8 (mk_usize 200) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize blocks
      (v_RATE -! mk_usize 1 <: usize)
      ((blocks.[ v_RATE -! mk_usize 1 <: usize ] <: u8) |. mk_u8 128 <: u8)
  in
  let self:t_KeccakXofState v_RATE =
    {
      self with
      f_inner
      =
      Libcrux_iot_sha3.State.impl_KeccakState__load_block_full v_RATE
        self.f_inner
        blocks
        (mk_usize 0)
    }
    <:
    t_KeccakXofState v_RATE
  in
  let self:t_KeccakXofState v_RATE =
    { self with f_inner = keccakf1600 self.f_inner } <: t_KeccakXofState v_RATE
  in
  self

let absorb_block
      (v_RATE: usize)
      (s: Libcrux_iot_sha3.State.t_KeccakState)
      (blocks: t_Slice u8)
      (start: usize)
    : Prims.Pure Libcrux_iot_sha3.State.t_KeccakState
      (requires
        (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 && v_RATE <=. mk_usize 168 &&
        ((Rust_primitives.Hax.Int.from_machine start <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine v_RATE <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine (Core_models.Slice.impl__len #u8 blocks <: usize)
          <:
          Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__load_block v_RATE s blocks start
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600 s in
  s

let absorb_final
      (v_RATE: usize)
      (v_DELIM: u8)
      (s: Libcrux_iot_sha3.State.t_KeccakState)
      (last: t_Slice u8)
      (start len: usize)
    : Prims.Pure Libcrux_iot_sha3.State.t_KeccakState
      (requires
        v_RATE >. mk_usize 0 && (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 &&
        v_RATE <=. mk_usize 168 &&
        len <. v_RATE &&
        ((Rust_primitives.Hax.Int.from_machine start <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine len <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine (Core_models.Slice.impl__len #u8 last <: usize)
          <:
          Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit = Hax_lib.v_assert (len <. v_RATE <: bool) in
      ()
  in
  let blocks:t_Array u8 (mk_usize 200) =
    Libcrux_secrets.Traits.f_classify #(t_Array u8 (mk_usize 200))
      #FStar.Tactics.Typeclasses.solve
      (Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 200) <: t_Array u8 (mk_usize 200))
  in
  let blocks:t_Array u8 (mk_usize 200) =
    if len >. mk_usize 0
    then
      let blocks:t_Array u8 (mk_usize 200) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_range blocks
          ({ Core_models.Ops.Range.f_start = mk_usize 0; Core_models.Ops.Range.f_end = len }
            <:
            Core_models.Ops.Range.t_Range usize)
          (Core_models.Slice.impl__copy_from_slice #u8
              (blocks.[ {
                    Core_models.Ops.Range.f_start = mk_usize 0;
                    Core_models.Ops.Range.f_end = len
                  }
                  <:
                  Core_models.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
              (last.[ {
                    Core_models.Ops.Range.f_start = start;
                    Core_models.Ops.Range.f_end = start +! len <: usize
                  }
                  <:
                  Core_models.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            t_Slice u8)
      in
      blocks
    else blocks
  in
  let blocks:t_Array u8 (mk_usize 200) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize blocks
      len
      (Libcrux_secrets.Traits.f_classify #u8 #FStar.Tactics.Typeclasses.solve v_DELIM <: u8)
  in
  let blocks:t_Array u8 (mk_usize 200) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize blocks
      (v_RATE -! mk_usize 1 <: usize)
      ((blocks.[ v_RATE -! mk_usize 1 <: usize ] <: u8) |. mk_u8 128 <: u8)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__load_block_full v_RATE s blocks (mk_usize 0)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600 s in
  s

let squeeze_first_block (v_RATE: usize) (s: Libcrux_iot_sha3.State.t_KeccakState) (out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 && v_RATE <=. mk_usize 168 &&
        v_RATE <=. (Core_models.Slice.impl__len #u8 out <: usize))
      (ensures
        fun out_future ->
          let out_future:t_Slice u8 = out_future in
          (Core_models.Slice.impl__len #u8 out_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out <: usize)) =
  let out:t_Slice u8 = Libcrux_iot_sha3.State.impl_KeccakState__store_block v_RATE s out in
  out

let squeeze_next_block (v_RATE: usize) (s: Libcrux_iot_sha3.State.t_KeccakState) (out: t_Slice u8)
    : Prims.Pure (Libcrux_iot_sha3.State.t_KeccakState & t_Slice u8)
      (requires
        (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 && v_RATE <=. mk_usize 168 &&
        v_RATE <=. (Core_models.Slice.impl__len #u8 out <: usize))
      (ensures
        fun temp_0_ ->
          let (s_future: Libcrux_iot_sha3.State.t_KeccakState), (out_future: t_Slice u8) =
            temp_0_
          in
          (Core_models.Slice.impl__len #u8 out_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out <: usize)) =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600 s in
  let out:t_Slice u8 = Libcrux_iot_sha3.State.impl_KeccakState__store_block v_RATE s out in
  s, out <: (Libcrux_iot_sha3.State.t_KeccakState & t_Slice u8)

let squeeze_first_three_blocks
      (v_RATE: usize)
      (s: Libcrux_iot_sha3.State.t_KeccakState)
      (out: t_Slice u8)
    : Prims.Pure (Libcrux_iot_sha3.State.t_KeccakState & t_Slice u8)
      (requires
        (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 && v_RATE <=. mk_usize 168 &&
        (mk_usize 3 *! v_RATE <: usize) <=. (Core_models.Slice.impl__len #u8 out <: usize))
      (ensures
        fun temp_0_ ->
          let (s_future: Libcrux_iot_sha3.State.t_KeccakState), (out_future: t_Slice u8) =
            temp_0_
          in
          (Core_models.Slice.impl__len #u8 out_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out <: usize)) =
  let out:t_Slice u8 = squeeze_first_block v_RATE s out in
  let (tmp0: Libcrux_iot_sha3.State.t_KeccakState), (tmp1: t_Slice u8) =
    squeeze_next_block v_RATE
      s
      (out.[ { Core_models.Ops.Range.f_start = v_RATE } <: Core_models.Ops.Range.t_RangeFrom usize ]
        <:
        t_Slice u8)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState = tmp0 in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from out
      ({ Core_models.Ops.Range.f_start = v_RATE } <: Core_models.Ops.Range.t_RangeFrom usize)
      tmp1
  in
  let _:Prims.unit = () in
  let (tmp0: Libcrux_iot_sha3.State.t_KeccakState), (tmp1: t_Slice u8) =
    squeeze_next_block v_RATE
      s
      (out.[ { Core_models.Ops.Range.f_start = mk_usize 2 *! v_RATE <: usize }
          <:
          Core_models.Ops.Range.t_RangeFrom usize ]
        <:
        t_Slice u8)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState = tmp0 in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from out
      ({ Core_models.Ops.Range.f_start = mk_usize 2 *! v_RATE <: usize }
        <:
        Core_models.Ops.Range.t_RangeFrom usize)
      tmp1
  in
  let _:Prims.unit = () in
  s, out <: (Libcrux_iot_sha3.State.t_KeccakState & t_Slice u8)

let squeeze_first_five_blocks
      (v_RATE: usize)
      (s: Libcrux_iot_sha3.State.t_KeccakState)
      (out: t_Slice u8)
    : Prims.Pure (Libcrux_iot_sha3.State.t_KeccakState & t_Slice u8)
      (requires
        (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 && v_RATE <=. mk_usize 168 &&
        (mk_usize 5 *! v_RATE <: usize) <=. (Core_models.Slice.impl__len #u8 out <: usize))
      (ensures
        fun temp_0_ ->
          let (s_future: Libcrux_iot_sha3.State.t_KeccakState), (out_future: t_Slice u8) =
            temp_0_
          in
          (Core_models.Slice.impl__len #u8 out_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out <: usize)) =
  let out:t_Slice u8 = squeeze_first_block v_RATE s out in
  let (tmp0: Libcrux_iot_sha3.State.t_KeccakState), (tmp1: t_Slice u8) =
    squeeze_next_block v_RATE
      s
      (out.[ { Core_models.Ops.Range.f_start = v_RATE } <: Core_models.Ops.Range.t_RangeFrom usize ]
        <:
        t_Slice u8)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState = tmp0 in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from out
      ({ Core_models.Ops.Range.f_start = v_RATE } <: Core_models.Ops.Range.t_RangeFrom usize)
      tmp1
  in
  let _:Prims.unit = () in
  let (tmp0: Libcrux_iot_sha3.State.t_KeccakState), (tmp1: t_Slice u8) =
    squeeze_next_block v_RATE
      s
      (out.[ { Core_models.Ops.Range.f_start = mk_usize 2 *! v_RATE <: usize }
          <:
          Core_models.Ops.Range.t_RangeFrom usize ]
        <:
        t_Slice u8)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState = tmp0 in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from out
      ({ Core_models.Ops.Range.f_start = mk_usize 2 *! v_RATE <: usize }
        <:
        Core_models.Ops.Range.t_RangeFrom usize)
      tmp1
  in
  let _:Prims.unit = () in
  let (tmp0: Libcrux_iot_sha3.State.t_KeccakState), (tmp1: t_Slice u8) =
    squeeze_next_block v_RATE
      s
      (out.[ { Core_models.Ops.Range.f_start = mk_usize 3 *! v_RATE <: usize }
          <:
          Core_models.Ops.Range.t_RangeFrom usize ]
        <:
        t_Slice u8)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState = tmp0 in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from out
      ({ Core_models.Ops.Range.f_start = mk_usize 3 *! v_RATE <: usize }
        <:
        Core_models.Ops.Range.t_RangeFrom usize)
      tmp1
  in
  let _:Prims.unit = () in
  let (tmp0: Libcrux_iot_sha3.State.t_KeccakState), (tmp1: t_Slice u8) =
    squeeze_next_block v_RATE
      s
      (out.[ { Core_models.Ops.Range.f_start = mk_usize 4 *! v_RATE <: usize }
          <:
          Core_models.Ops.Range.t_RangeFrom usize ]
        <:
        t_Slice u8)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState = tmp0 in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from out
      ({ Core_models.Ops.Range.f_start = mk_usize 4 *! v_RATE <: usize }
        <:
        Core_models.Ops.Range.t_RangeFrom usize)
      tmp1
  in
  let _:Prims.unit = () in
  s, out <: (Libcrux_iot_sha3.State.t_KeccakState & t_Slice u8)

let squeeze_last (v_RATE: usize) (s: Libcrux_iot_sha3.State.t_KeccakState) (out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 && v_RATE <=. mk_usize 168 &&
        (Core_models.Slice.impl__len #u8 out <: usize) <=. mk_usize 200)
      (ensures
        fun out_future ->
          let out_future:t_Slice u8 = out_future in
          (Core_models.Slice.impl__len #u8 out_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out <: usize)) =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600 s in
  let b:t_Array u8 (mk_usize 200) =
    Libcrux_secrets.Traits.f_classify #(t_Array u8 (mk_usize 200))
      #FStar.Tactics.Typeclasses.solve
      (Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 200) <: t_Array u8 (mk_usize 200))
  in
  let b:t_Array u8 (mk_usize 200) =
    Libcrux_iot_sha3.State.impl_KeccakState__store_block_full v_RATE s b
  in
  let out:t_Slice u8 =
    Core_models.Slice.impl__copy_from_slice #u8
      out
      (b.[ {
            Core_models.Ops.Range.f_start = mk_usize 0;
            Core_models.Ops.Range.f_end = Core_models.Slice.impl__len #u8 out <: usize
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  out

let squeeze_first_and_last
      (v_RATE: usize)
      (s: Libcrux_iot_sha3.State.t_KeccakState)
      (out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 && v_RATE <=. mk_usize 168 &&
        (Core_models.Slice.impl__len #u8 out <: usize) <=. mk_usize 200)
      (ensures
        fun out_future ->
          let out_future:t_Slice u8 = out_future in
          (Core_models.Slice.impl__len #u8 out_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out <: usize)) =
  let b:t_Array u8 (mk_usize 200) =
    Libcrux_secrets.Traits.f_classify #(t_Array u8 (mk_usize 200))
      #FStar.Tactics.Typeclasses.solve
      (Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 200) <: t_Array u8 (mk_usize 200))
  in
  let b:t_Array u8 (mk_usize 200) =
    Libcrux_iot_sha3.State.impl_KeccakState__store_block_full v_RATE s b
  in
  let out:t_Slice u8 =
    Core_models.Slice.impl__copy_from_slice #u8
      out
      (b.[ {
            Core_models.Ops.Range.f_start = mk_usize 0;
            Core_models.Ops.Range.f_end = Core_models.Slice.impl__len #u8 out <: usize
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  out

let v_WIDTH: usize = mk_usize 200

let keccak (v_RATE: usize) (v_DELIM: u8) (data out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        v_RATE >. mk_usize 0 && (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 &&
        v_RATE <=. mk_usize 168)
      (ensures
        fun out_future ->
          let out_future:t_Slice u8 = out_future in
          (Core_models.Slice.impl__len #u8 out_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out <: usize)) =
  let n:usize = (Core_models.Slice.impl__len #u8 data <: usize) /! v_RATE in
  let rem:usize = (Core_models.Slice.impl__len #u8 data <: usize) %! v_RATE in
  let outlen:usize = Core_models.Slice.impl__len #u8 out in
  let blocks:usize = outlen /! v_RATE in
  let last:usize = outlen -! (outlen %! v_RATE <: usize) in
  let s:Libcrux_iot_sha3.State.t_KeccakState = Libcrux_iot_sha3.State.impl_KeccakState__new () in
  let start:usize = mk_usize 0 in
  let (s: Libcrux_iot_sha3.State.t_KeccakState), (start: usize) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      n
      (fun temp_0_ e_i ->
          let (s: Libcrux_iot_sha3.State.t_KeccakState), (start: usize) = temp_0_ in
          let e_i:usize = e_i in
          (Rust_primitives.Hax.Int.from_machine start <: Hax_lib.Int.t_Int) =
          ((Rust_primitives.Hax.Int.from_machine e_i <: Hax_lib.Int.t_Int) *
            (Rust_primitives.Hax.Int.from_machine v_RATE <: Hax_lib.Int.t_Int)
            <:
            Hax_lib.Int.t_Int)
          <:
          bool)
      (s, start <: (Libcrux_iot_sha3.State.t_KeccakState & usize))
      (fun temp_0_ e_i ->
          let (s: Libcrux_iot_sha3.State.t_KeccakState), (start: usize) = temp_0_ in
          let e_i:usize = e_i in
          let s:Libcrux_iot_sha3.State.t_KeccakState = absorb_block v_RATE s data start in
          let start:usize = start +! v_RATE in
          s, start <: (Libcrux_iot_sha3.State.t_KeccakState & usize))
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    absorb_final v_RATE
      v_DELIM
      s
      data
      ((Core_models.Slice.impl__len #u8 data <: usize) -! rem <: usize)
      rem
  in
  let (out: t_Slice u8), (s: Libcrux_iot_sha3.State.t_KeccakState) =
    if blocks =. mk_usize 0
    then
      squeeze_first_and_last v_RATE s out, s <: (t_Slice u8 & Libcrux_iot_sha3.State.t_KeccakState)
    else
      let out:t_Slice u8 = squeeze_first_block v_RATE s out in
      let offset:usize = v_RATE in
      let (offset: usize), (out: t_Slice u8), (s: Libcrux_iot_sha3.State.t_KeccakState) =
        Rust_primitives.Hax.Folds.fold_range (mk_usize 1)
          blocks
          (fun temp_0_ e_i ->
              let (offset: usize), (out: t_Slice u8), (s: Libcrux_iot_sha3.State.t_KeccakState) =
                temp_0_
              in
              let e_i:usize = e_i in
              ((Core_models.Slice.impl__len #u8 out <: usize) =. outlen <: bool) &&
              ((Rust_primitives.Hax.Int.from_machine offset <: Hax_lib.Int.t_Int) =
                ((Rust_primitives.Hax.Int.from_machine e_i <: Hax_lib.Int.t_Int) *
                  (Rust_primitives.Hax.Int.from_machine v_RATE <: Hax_lib.Int.t_Int)
                  <:
                  Hax_lib.Int.t_Int)
                <:
                bool))
          (offset, out, s <: (usize & t_Slice u8 & Libcrux_iot_sha3.State.t_KeccakState))
          (fun temp_0_ e_i ->
              let (offset: usize), (out: t_Slice u8), (s: Libcrux_iot_sha3.State.t_KeccakState) =
                temp_0_
              in
              let e_i:usize = e_i in
              let (tmp0: Libcrux_iot_sha3.State.t_KeccakState), (tmp1: t_Slice u8) =
                squeeze_next_block v_RATE
                  s
                  (out.[ { Core_models.Ops.Range.f_start = offset }
                      <:
                      Core_models.Ops.Range.t_RangeFrom usize ]
                    <:
                    t_Slice u8)
              in
              let s:Libcrux_iot_sha3.State.t_KeccakState = tmp0 in
              let out:t_Slice u8 =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from out
                  ({ Core_models.Ops.Range.f_start = offset }
                    <:
                    Core_models.Ops.Range.t_RangeFrom usize)
                  tmp1
              in
              let _:Prims.unit = () in
              let offset:usize = offset +! v_RATE in
              offset, out, s <: (usize & t_Slice u8 & Libcrux_iot_sha3.State.t_KeccakState))
      in
      if last <. outlen
      then
        let _:Prims.unit =
          if true
          then
            let _:Prims.unit =
              match last, offset <: (usize & usize) with
              | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
            in
            ()
        in
        Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from out
          ({ Core_models.Ops.Range.f_start = offset } <: Core_models.Ops.Range.t_RangeFrom usize)
          (squeeze_last v_RATE
              s
              (out.[ { Core_models.Ops.Range.f_start = offset }
                  <:
                  Core_models.Ops.Range.t_RangeFrom usize ]
                <:
                t_Slice u8)
            <:
            t_Slice u8),
        s
        <:
        (t_Slice u8 & Libcrux_iot_sha3.State.t_KeccakState)
      else out, s <: (t_Slice u8 & Libcrux_iot_sha3.State.t_KeccakState)
  in
  out
