module Libcrux_secrets.Int.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_secrets.Int.Public_integers in
  let open Libcrux_secrets.Traits in
  ()

let is_non_zero_32_ (selector: u8) : u32 =
  Core.Hint.black_box #u32
    (((Core.Num.impl_u32__wrapping_add (~.(cast (Core.Hint.black_box #u8 selector <: u8) <: u32)
              <:
              u32)
            (mk_u32 1)
          <:
          u32) >>!
        mk_i32 31
        <:
        u32) &.
      mk_u32 1
      <:
      u32)

let is_non_zero_64_ (selector: u8) : u64 =
  Core.Hint.black_box #u64
    (((Core.Num.impl_u64__wrapping_add (~.(cast (Core.Hint.black_box #u8 selector <: u8) <: u64)
              <:
              u64)
            (mk_u64 1)
          <:
          u64) >>!
        mk_i32 63
        <:
        u64) &.
      mk_u64 1
      <:
      u64)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Libcrux_secrets.Int.t_Select (t_Slice u8) =
  {
    f_select_pre = (fun (self: t_Slice u8) (other: t_Slice u8) (selector: u8) -> true);
    f_select_post
    =
    (fun (self: t_Slice u8) (other: t_Slice u8) (selector: u8) (out: t_Slice u8) -> true);
    f_select
    =
    fun (self: t_Slice u8) (other: t_Slice u8) (selector: u8) ->
      let mask:u8 =
        Core.Num.impl_u8__wrapping_sub (cast (is_non_zero_32_ (Libcrux_secrets.Traits.f_declassify #u8
                      #FStar.Tactics.Typeclasses.solve
                      selector
                    <:
                    u8)
                <:
                u32)
            <:
            u8)
          (mk_u8 1)
      in
      let self:t_Slice u8 =
        Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
          (Core.Slice.impl__len #u8 self <: usize)
          (fun self temp_1_ ->
              let self:t_Slice u8 = self in
              let _:usize = temp_1_ in
              true)
          self
          (fun self i ->
              let self:t_Slice u8 = self in
              let i:usize = i in
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self
                i
                (((self.[ i ] <: u8) &. mask <: u8) |. ((other.[ i ] <: u8) &. (~.mask <: u8) <: u8)
                  <:
                  u8)
              <:
              t_Slice u8)
      in
      self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Libcrux_secrets.Int.t_Select (t_Slice u16) =
  {
    f_select_pre = (fun (self: t_Slice u16) (other: t_Slice u16) (selector: u8) -> true);
    f_select_post
    =
    (fun (self: t_Slice u16) (other: t_Slice u16) (selector: u8) (out: t_Slice u16) -> true);
    f_select
    =
    fun (self: t_Slice u16) (other: t_Slice u16) (selector: u8) ->
      let mask:u16 =
        Core.Num.impl_u16__wrapping_sub (cast (is_non_zero_32_ (Libcrux_secrets.Traits.f_declassify #u8
                      #FStar.Tactics.Typeclasses.solve
                      selector
                    <:
                    u8)
                <:
                u32)
            <:
            u16)
          (mk_u16 1)
      in
      let self:t_Slice u16 =
        Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
          (Core.Slice.impl__len #u16 self <: usize)
          (fun self temp_1_ ->
              let self:t_Slice u16 = self in
              let _:usize = temp_1_ in
              true)
          self
          (fun self i ->
              let self:t_Slice u16 = self in
              let i:usize = i in
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self
                i
                (((self.[ i ] <: u16) &. mask <: u16) |.
                  ((other.[ i ] <: u16) &. (~.mask <: u16) <: u16)
                  <:
                  u16)
              <:
              t_Slice u16)
      in
      self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Libcrux_secrets.Int.t_Select (t_Slice u32) =
  {
    f_select_pre = (fun (self: t_Slice u32) (other: t_Slice u32) (selector: u8) -> true);
    f_select_post
    =
    (fun (self: t_Slice u32) (other: t_Slice u32) (selector: u8) (out: t_Slice u32) -> true);
    f_select
    =
    fun (self: t_Slice u32) (other: t_Slice u32) (selector: u8) ->
      let mask:u32 =
        Core.Num.impl_u32__wrapping_sub (is_non_zero_32_ (Libcrux_secrets.Traits.f_declassify #u8
                  #FStar.Tactics.Typeclasses.solve
                  selector
                <:
                u8)
            <:
            u32)
          (mk_u32 1)
      in
      let self:t_Slice u32 =
        Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
          (Core.Slice.impl__len #u32 self <: usize)
          (fun self temp_1_ ->
              let self:t_Slice u32 = self in
              let _:usize = temp_1_ in
              true)
          self
          (fun self i ->
              let self:t_Slice u32 = self in
              let i:usize = i in
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self
                i
                (((self.[ i ] <: u32) &. mask <: u32) |.
                  ((other.[ i ] <: u32) &. (~.mask <: u32) <: u32)
                  <:
                  u32)
              <:
              t_Slice u32)
      in
      self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Libcrux_secrets.Int.t_Select (t_Slice u64) =
  {
    f_select_pre = (fun (self: t_Slice u64) (other: t_Slice u64) (selector: u8) -> true);
    f_select_post
    =
    (fun (self: t_Slice u64) (other: t_Slice u64) (selector: u8) (out: t_Slice u64) -> true);
    f_select
    =
    fun (self: t_Slice u64) (other: t_Slice u64) (selector: u8) ->
      let mask:u64 =
        Core.Num.impl_u64__wrapping_sub (is_non_zero_64_ (Libcrux_secrets.Traits.f_declassify #u8
                  #FStar.Tactics.Typeclasses.solve
                  selector
                <:
                u8)
            <:
            u64)
          (mk_u64 1)
      in
      let self:t_Slice u64 =
        Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
          (Core.Slice.impl__len #u64 self <: usize)
          (fun self temp_1_ ->
              let self:t_Slice u64 = self in
              let _:usize = temp_1_ in
              true)
          self
          (fun self i ->
              let self:t_Slice u64 = self in
              let i:usize = i in
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self
                i
                (((self.[ i ] <: u64) &. mask <: u64) |.
                  ((other.[ i ] <: u64) &. (~.mask <: u64) <: u64)
                  <:
                  u64)
              <:
              t_Slice u64)
      in
      self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: Libcrux_secrets.Int.t_Swap (t_Slice u8) =
  {
    f_cswap_pre = (fun (self: t_Slice u8) (other: t_Slice u8) (selector: u8) -> true);
    f_cswap_post
    =
    (fun (self: t_Slice u8) (other: t_Slice u8) (selector: u8) (out: (t_Slice u8 & t_Slice u8)) ->
        true);
    f_cswap
    =
    fun (self: t_Slice u8) (other: t_Slice u8) (selector: u8) ->
      let _:Prims.unit =
        if true
        then
          let _:Prims.unit =
            match
              Core.Slice.impl__len #u8 self, Core.Slice.impl__len #u8 other <: (usize & usize)
            with
            | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
          in
          ()
      in
      let mask:u8 =
        Core.Hint.black_box #u8
          (Core.Num.impl_u8__wrapping_sub (cast (((Core.Num.impl_u32__wrapping_add (~.(cast (Core.Hint.black_box
                                    #u8
                                    (Libcrux_secrets.Traits.f_declassify #u8
                                        #FStar.Tactics.Typeclasses.solve
                                        selector
                                      <:
                                      u8)
                                  <:
                                  u8)
                              <:
                              u32)
                            <:
                            u32)
                          (mk_u32 1)
                        <:
                        u32) >>!
                      mk_i32 31
                      <:
                      u32) &.
                    mk_u32 1
                    <:
                    u32)
                <:
                u8)
              (mk_u8 1)
            <:
            u8)
      in
      let other, self:(t_Slice u8 & t_Slice u8) =
        Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
          (Core.Slice.impl__len #u8 self <: usize)
          (fun temp_0_ temp_1_ ->
              let other, self:(t_Slice u8 & t_Slice u8) = temp_0_ in
              let _:usize = temp_1_ in
              true)
          (other, self <: (t_Slice u8 & t_Slice u8))
          (fun temp_0_ i ->
              let other, self:(t_Slice u8 & t_Slice u8) = temp_0_ in
              let i:usize = i in
              let dummy:u8 = (~.mask <: u8) &. ((self.[ i ] <: u8) ^. (other.[ i ] <: u8) <: u8) in
              let self:t_Slice u8 =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self
                  i
                  ((self.[ i ] <: u8) ^. dummy <: u8)
              in
              let other:t_Slice u8 =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize other
                  i
                  ((other.[ i ] <: u8) ^. dummy <: u8)
              in
              other, self <: (t_Slice u8 & t_Slice u8))
      in
      self, other <: (t_Slice u8 & t_Slice u8)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: Libcrux_secrets.Int.t_Swap (t_Slice u16) =
  {
    f_cswap_pre = (fun (self: t_Slice u16) (other: t_Slice u16) (selector: u8) -> true);
    f_cswap_post
    =
    (fun
        (self: t_Slice u16)
        (other: t_Slice u16)
        (selector: u8)
        (out: (t_Slice u16 & t_Slice u16))
        ->
        true);
    f_cswap
    =
    fun (self: t_Slice u16) (other: t_Slice u16) (selector: u8) ->
      let _:Prims.unit =
        if true
        then
          let _:Prims.unit =
            match
              Core.Slice.impl__len #u16 self, Core.Slice.impl__len #u16 other <: (usize & usize)
            with
            | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
          in
          ()
      in
      let mask:u16 =
        Core.Hint.black_box #u16
          (Core.Num.impl_u16__wrapping_sub (cast (((Core.Num.impl_u32__wrapping_add (~.(cast (Core.Hint.black_box
                                    #u8
                                    (Libcrux_secrets.Traits.f_declassify #u8
                                        #FStar.Tactics.Typeclasses.solve
                                        selector
                                      <:
                                      u8)
                                  <:
                                  u8)
                              <:
                              u32)
                            <:
                            u32)
                          (mk_u32 1)
                        <:
                        u32) >>!
                      mk_i32 31
                      <:
                      u32) &.
                    mk_u32 1
                    <:
                    u32)
                <:
                u16)
              (mk_u16 1)
            <:
            u16)
      in
      let other, self:(t_Slice u16 & t_Slice u16) =
        Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
          (Core.Slice.impl__len #u16 self <: usize)
          (fun temp_0_ temp_1_ ->
              let other, self:(t_Slice u16 & t_Slice u16) = temp_0_ in
              let _:usize = temp_1_ in
              true)
          (other, self <: (t_Slice u16 & t_Slice u16))
          (fun temp_0_ i ->
              let other, self:(t_Slice u16 & t_Slice u16) = temp_0_ in
              let i:usize = i in
              let dummy:u16 =
                (~.mask <: u16) &. ((self.[ i ] <: u16) ^. (other.[ i ] <: u16) <: u16)
              in
              let self:t_Slice u16 =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self
                  i
                  ((self.[ i ] <: u16) ^. dummy <: u16)
              in
              let other:t_Slice u16 =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize other
                  i
                  ((other.[ i ] <: u16) ^. dummy <: u16)
              in
              other, self <: (t_Slice u16 & t_Slice u16))
      in
      self, other <: (t_Slice u16 & t_Slice u16)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: Libcrux_secrets.Int.t_Swap (t_Slice u32) =
  {
    f_cswap_pre = (fun (self: t_Slice u32) (other: t_Slice u32) (selector: u8) -> true);
    f_cswap_post
    =
    (fun
        (self: t_Slice u32)
        (other: t_Slice u32)
        (selector: u8)
        (out: (t_Slice u32 & t_Slice u32))
        ->
        true);
    f_cswap
    =
    fun (self: t_Slice u32) (other: t_Slice u32) (selector: u8) ->
      let _:Prims.unit =
        if true
        then
          let _:Prims.unit =
            match
              Core.Slice.impl__len #u32 self, Core.Slice.impl__len #u32 other <: (usize & usize)
            with
            | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
          in
          ()
      in
      let mask:u32 =
        Core.Hint.black_box #u32
          (Core.Num.impl_u32__wrapping_sub (((Core.Num.impl_u32__wrapping_add (~.(cast (Core.Hint.black_box
                                #u8
                                (Libcrux_secrets.Traits.f_declassify #u8
                                    #FStar.Tactics.Typeclasses.solve
                                    selector
                                  <:
                                  u8)
                              <:
                              u8)
                          <:
                          u32)
                        <:
                        u32)
                      (mk_u32 1)
                    <:
                    u32) >>!
                  mk_i32 31
                  <:
                  u32) &.
                mk_u32 1
                <:
                u32)
              (mk_u32 1)
            <:
            u32)
      in
      let other, self:(t_Slice u32 & t_Slice u32) =
        Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
          (Core.Slice.impl__len #u32 self <: usize)
          (fun temp_0_ temp_1_ ->
              let other, self:(t_Slice u32 & t_Slice u32) = temp_0_ in
              let _:usize = temp_1_ in
              true)
          (other, self <: (t_Slice u32 & t_Slice u32))
          (fun temp_0_ i ->
              let other, self:(t_Slice u32 & t_Slice u32) = temp_0_ in
              let i:usize = i in
              let dummy:u32 =
                (~.mask <: u32) &. ((self.[ i ] <: u32) ^. (other.[ i ] <: u32) <: u32)
              in
              let self:t_Slice u32 =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self
                  i
                  ((self.[ i ] <: u32) ^. dummy <: u32)
              in
              let other:t_Slice u32 =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize other
                  i
                  ((other.[ i ] <: u32) ^. dummy <: u32)
              in
              other, self <: (t_Slice u32 & t_Slice u32))
      in
      self, other <: (t_Slice u32 & t_Slice u32)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7: Libcrux_secrets.Int.t_Swap (t_Slice u64) =
  {
    f_cswap_pre = (fun (self: t_Slice u64) (other: t_Slice u64) (selector: u8) -> true);
    f_cswap_post
    =
    (fun
        (self: t_Slice u64)
        (other: t_Slice u64)
        (selector: u8)
        (out: (t_Slice u64 & t_Slice u64))
        ->
        true);
    f_cswap
    =
    fun (self: t_Slice u64) (other: t_Slice u64) (selector: u8) ->
      let _:Prims.unit =
        if true
        then
          let _:Prims.unit =
            match
              Core.Slice.impl__len #u64 self, Core.Slice.impl__len #u64 other <: (usize & usize)
            with
            | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
          in
          ()
      in
      let mask:u64 =
        Core.Hint.black_box #u64
          (Core.Num.impl_u64__wrapping_sub (((Core.Num.impl_u64__wrapping_add (~.(cast (Libcrux_secrets.Traits.f_declassify
                                #u8
                                #FStar.Tactics.Typeclasses.solve
                                selector
                              <:
                              u8)
                          <:
                          u64)
                        <:
                        u64)
                      (mk_u64 1)
                    <:
                    u64) >>!
                  mk_i32 63
                  <:
                  u64) &.
                mk_u64 1
                <:
                u64)
              (mk_u64 1)
            <:
            u64)
      in
      let other, self:(t_Slice u64 & t_Slice u64) =
        Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
          (Core.Slice.impl__len #u64 self <: usize)
          (fun temp_0_ temp_1_ ->
              let other, self:(t_Slice u64 & t_Slice u64) = temp_0_ in
              let _:usize = temp_1_ in
              true)
          (other, self <: (t_Slice u64 & t_Slice u64))
          (fun temp_0_ i ->
              let other, self:(t_Slice u64 & t_Slice u64) = temp_0_ in
              let i:usize = i in
              let dummy:u64 =
                (~.mask <: u64) &. ((self.[ i ] <: u64) ^. (other.[ i ] <: u64) <: u64)
              in
              let self:t_Slice u64 =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self
                  i
                  ((self.[ i ] <: u64) ^. dummy <: u64)
              in
              let other:t_Slice u64 =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize other
                  i
                  ((other.[ i ] <: u64) ^. dummy <: u64)
              in
              other, self <: (t_Slice u64 & t_Slice u64))
      in
      self, other <: (t_Slice u64 & t_Slice u64)
  }
