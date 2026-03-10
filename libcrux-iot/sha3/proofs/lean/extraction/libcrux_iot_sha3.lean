import extraction.helpers

-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace libcrux_iot_sha3.keccak

--  An all zero block
@[spec]
def Impl.zero_block (RATE : usize) (_ : rust_primitives.hax.Tuple0) :
    RustM (RustArray u8 RATE) := do
  (libcrux_secrets.traits.Classify.classify
    (RustArray u8 RATE) (← (rust_primitives.hax.repeat (0 : u8) RATE)))

set_option maxRecDepth 1000 in

def RC_INTERLEAVED_0 : (RustArray u32 255) :=
  RustM.of_isOk
    (do
    (pure (RustArray.ofVec #v[(1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32),
                                (1 : u32),
                                (0 : u32),
                                (1 : u32),
                                (1 : u32),
                                (1 : u32),
                                (0 : u32),
                                (0 : u32),
                                (0 : u32)])))
    (by rfl)

set_option maxRecDepth 1000 in

def RC_INTERLEAVED_1 : (RustArray u32 255) :=
  RustM.of_isOk
    (do
    (pure (RustArray.ofVec #v[(0 : u32),
                                (137 : u32),
                                (2147483787 : u32),
                                (2147516544 : u32),
                                (139 : u32),
                                (32768 : u32),
                                (2147516552 : u32),
                                (2147483778 : u32),
                                (11 : u32),
                                (10 : u32),
                                (32898 : u32),
                                (32771 : u32),
                                (32907 : u32),
                                (2147483659 : u32),
                                (2147483786 : u32),
                                (2147483777 : u32),
                                (2147483777 : u32),
                                (2147483656 : u32),
                                (131 : u32),
                                (2147516419 : u32),
                                (2147516552 : u32),
                                (2147483784 : u32),
                                (32768 : u32),
                                (2147516546 : u32),
                                (2147516553 : u32),
                                (2147516547 : u32),
                                (2147483649 : u32),
                                (2147516418 : u32),
                                (2147483785 : u32),
                                (130 : u32),
                                (2147483656 : u32),
                                (137 : u32),
                                (2147483656 : u32),
                                (0 : u32),
                                (131 : u32),
                                (2147516544 : u32),
                                (8 : u32),
                                (2147483776 : u32),
                                (2147516544 : u32),
                                (2 : u32),
                                (2147516555 : u32),
                                (8 : u32),
                                (2147483657 : u32),
                                (32779 : u32),
                                (2147516546 : u32),
                                (2147516416 : u32),
                                (32776 : u32),
                                (32897 : u32),
                                (2147516553 : u32),
                                (2147516553 : u32),
                                (2147516426 : u32),
                                (138 : u32),
                                (130 : u32),
                                (2147483650 : u32),
                                (32898 : u32),
                                (32896 : u32),
                                (2147483659 : u32),
                                (2147483651 : u32),
                                (10 : u32),
                                (32769 : u32),
                                (2147483779 : u32),
                                (32899 : u32),
                                (139 : u32),
                                (32778 : u32),
                                (2147483779 : u32),
                                (32778 : u32),
                                (2147483648 : u32),
                                (2147483786 : u32),
                                (2147483656 : u32),
                                (10 : u32),
                                (32904 : u32),
                                (8 : u32),
                                (2147483651 : u32),
                                (0 : u32),
                                (10 : u32),
                                (32779 : u32),
                                (2147516552 : u32),
                                (2147483659 : u32),
                                (2147483776 : u32),
                                (2147516554 : u32),
                                (32777 : u32),
                                (3 : u32),
                                (2147483651 : u32),
                                (137 : u32),
                                (2147483777 : u32),
                                (2147483787 : u32),
                                (2147516419 : u32),
                                (2147516427 : u32),
                                (32776 : u32),
                                (32776 : u32),
                                (32770 : u32),
                                (9 : u32),
                                (2147516545 : u32),
                                (32906 : u32),
                                (2147516426 : u32),
                                (128 : u32),
                                (32905 : u32),
                                (32906 : u32),
                                (2147516553 : u32),
                                (2147516416 : u32),
                                (32897 : u32),
                                (2147516426 : u32),
                                (9 : u32),
                                (2147516418 : u32),
                                (2147483658 : u32),
                                (2147516418 : u32),
                                (2147483648 : u32),
                                (2147483657 : u32),
                                (32904 : u32),
                                (2 : u32),
                                (2147516424 : u32),
                                (2147516552 : u32),
                                (2147483649 : u32),
                                (2147516555 : u32),
                                (2 : u32),
                                (2147516418 : u32),
                                (2147483779 : u32),
                                (32905 : u32),
                                (32896 : u32),
                                (2147483778 : u32),
                                (136 : u32),
                                (2147516554 : u32),
                                (32906 : u32),
                                (2147516547 : u32),
                                (2147483659 : u32),
                                (2147483657 : u32),
                                (32769 : u32),
                                (2147483785 : u32),
                                (136 : u32),
                                (2147516419 : u32),
                                (2147516417 : u32),
                                (3 : u32),
                                (2147483776 : u32),
                                (2147516425 : u32),
                                (2147483785 : u32),
                                (11 : u32),
                                (131 : u32),
                                (2147516425 : u32),
                                (2147483779 : u32),
                                (32768 : u32),
                                (2147516427 : u32),
                                (32770 : u32),
                                (3 : u32),
                                (2147483786 : u32),
                                (2147483650 : u32),
                                (32769 : u32),
                                (2147483648 : u32),
                                (2147483651 : u32),
                                (131 : u32),
                                (2147516554 : u32),
                                (32771 : u32),
                                (32776 : u32),
                                (32907 : u32),
                                (2147483778 : u32),
                                (1 : u32),
                                (32769 : u32),
                                (2147483658 : u32),
                                (2147516424 : u32),
                                (2147516427 : u32),
                                (32897 : u32),
                                (2147516547 : u32),
                                (2147483778 : u32),
                                (130 : u32),
                                (2147483777 : u32),
                                (2147483650 : u32),
                                (32904 : u32),
                                (139 : u32),
                                (32899 : u32),
                                (8 : u32),
                                (2147483786 : u32),
                                (2147483787 : u32),
                                (2147516554 : u32),
                                (32896 : u32),
                                (2147483784 : u32),
                                (32899 : u32),
                                (2 : u32),
                                (2147516545 : u32),
                                (32771 : u32),
                                (32897 : u32),
                                (2147516416 : u32),
                                (32770 : u32),
                                (138 : u32),
                                (1 : u32),
                                (32898 : u32),
                                (32906 : u32),
                                (2147516416 : u32),
                                (32907 : u32),
                                (2147483649 : u32),
                                (2147516545 : u32),
                                (32777 : u32),
                                (138 : u32),
                                (136 : u32),
                                (2147516425 : u32),
                                (2147483658 : u32),
                                (2147516555 : u32),
                                (139 : u32),
                                (32905 : u32),
                                (32771 : u32),
                                (32770 : u32),
                                (128 : u32),
                                (32778 : u32),
                                (2147483658 : u32),
                                (2147516545 : u32),
                                (32896 : u32),
                                (2147483649 : u32),
                                (2147516424 : u32),
                                (2147516546 : u32),
                                (2147516426 : u32),
                                (3 : u32),
                                (2147483657 : u32),
                                (32898 : u32),
                                (32777 : u32),
                                (128 : u32),
                                (32899 : u32),
                                (129 : u32),
                                (1 : u32),
                                (32779 : u32),
                                (2147516417 : u32),
                                (128 : u32),
                                (32768 : u32),
                                (2147516417 : u32),
                                (9 : u32),
                                (2147516555 : u32),
                                (129 : u32),
                                (130 : u32),
                                (2147483787 : u32),
                                (2147516425 : u32),
                                (2147483648 : u32),
                                (2147483776 : u32),
                                (2147516419 : u32),
                                (2147516546 : u32),
                                (2147516547 : u32),
                                (2147483784 : u32),
                                (32905 : u32),
                                (32777 : u32),
                                (9 : u32),
                                (2147516424 : u32),
                                (2147516417 : u32),
                                (138 : u32),
                                (11 : u32),
                                (137 : u32),
                                (2147483650 : u32),
                                (32779 : u32),
                                (2147516427 : u32),
                                (32907 : u32),
                                (2147483784 : u32),
                                (32778 : u32),
                                (2147483785 : u32),
                                (1 : u32),
                                (32904 : u32),
                                (129 : u32),
                                (136 : u32),
                                (2147516544 : u32),
                                (129 : u32),
                                (11 : u32)])))
    (by rfl)

def WIDTH : usize := RustM.of_isOk (do (pure (200 : usize))) (by rfl)

end libcrux_iot_sha3.keccak


namespace libcrux_iot_sha3.lane

--  A lane of the Keccak state,
structure Lane2U32 where
  _0 : (RustArray u32 2)

@[instance] opaque Impl_3.AssociatedTypes :
  core_models.clone.Clone.AssociatedTypes Lane2U32 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3 :
  core_models.clone.Clone Lane2U32 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4.AssociatedTypes :
  core_models.marker.Copy.AssociatedTypes Lane2U32 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4 :
  core_models.marker.Copy Lane2U32 :=
  by constructor <;> exact Inhabited.default

@[spec]
def Impl.from_ints (value : (RustArray u32 2)) : RustM Lane2U32 := do
  (pure (Lane2U32.mk value))

@[spec]
def Impl.zero (_ : rust_primitives.hax.Tuple0) : RustM Lane2U32 := do
  (Impl.from_ints
    (← (libcrux_secrets.traits.Classify.classify
      (RustArray u32 2) (RustArray.ofVec #v[(0 : u32), (0 : u32)]))))

@[spec]
def Impl.deinterleave (self : Lane2U32) : RustM Lane2U32 := do
  let even_bits : u32 ← (Lane2U32._0 self)[(0 : usize)]_?;
  let odd_bits : u32 ← (Lane2U32._0 self)[(1 : usize)]_?;
  let even_spaced_lo : u32 ← (even_bits &&&? (65535 : u32));
  let even_spaced_lo : u32 ←
    ((← (even_spaced_lo ^^^? (← (even_spaced_lo <<<? (16 : i32)))))
      &&&? (65535 : u32));
  let even_spaced_lo : u32 ←
    ((← (even_spaced_lo ^^^? (← (even_spaced_lo <<<? (8 : i32)))))
      &&&? (16711935 : u32));
  let even_spaced_lo : u32 ←
    ((← (even_spaced_lo ^^^? (← (even_spaced_lo <<<? (4 : i32)))))
      &&&? (252645135 : u32));
  let even_spaced_lo : u32 ←
    ((← (even_spaced_lo ^^^? (← (even_spaced_lo <<<? (2 : i32)))))
      &&&? (858993459 : u32));
  let even_spaced_lo : u32 ←
    ((← (even_spaced_lo ^^^? (← (even_spaced_lo <<<? (1 : i32)))))
      &&&? (1431655765 : u32));
  let even_spaced_hi : u32 ← (even_bits >>>? (16 : i32));
  let even_spaced_hi : u32 ←
    ((← (even_spaced_hi ^^^? (← (even_spaced_hi <<<? (16 : i32)))))
      &&&? (65535 : u32));
  let even_spaced_hi : u32 ←
    ((← (even_spaced_hi ^^^? (← (even_spaced_hi <<<? (8 : i32)))))
      &&&? (16711935 : u32));
  let even_spaced_hi : u32 ←
    ((← (even_spaced_hi ^^^? (← (even_spaced_hi <<<? (4 : i32)))))
      &&&? (252645135 : u32));
  let even_spaced_hi : u32 ←
    ((← (even_spaced_hi ^^^? (← (even_spaced_hi <<<? (2 : i32)))))
      &&&? (858993459 : u32));
  let even_spaced_hi : u32 ←
    ((← (even_spaced_hi ^^^? (← (even_spaced_hi <<<? (1 : i32)))))
      &&&? (1431655765 : u32));
  let odd_spaced_lo : u32 ← (odd_bits &&&? (65535 : u32));
  let odd_spaced_lo : u32 ←
    ((← (odd_spaced_lo ^^^? (← (odd_spaced_lo <<<? (16 : i32)))))
      &&&? (65535 : u32));
  let odd_spaced_lo : u32 ←
    ((← (odd_spaced_lo ^^^? (← (odd_spaced_lo <<<? (8 : i32)))))
      &&&? (16711935 : u32));
  let odd_spaced_lo : u32 ←
    ((← (odd_spaced_lo ^^^? (← (odd_spaced_lo <<<? (4 : i32)))))
      &&&? (252645135 : u32));
  let odd_spaced_lo : u32 ←
    ((← (odd_spaced_lo ^^^? (← (odd_spaced_lo <<<? (2 : i32)))))
      &&&? (858993459 : u32));
  let odd_spaced_lo : u32 ←
    ((← (odd_spaced_lo ^^^? (← (odd_spaced_lo <<<? (1 : i32)))))
      &&&? (1431655765 : u32));
  let odd_spaced_hi : u32 ← (odd_bits >>>? (16 : i32));
  let odd_spaced_hi : u32 ←
    ((← (odd_spaced_hi ^^^? (← (odd_spaced_hi <<<? (16 : i32)))))
      &&&? (65535 : u32));
  let odd_spaced_hi : u32 ←
    ((← (odd_spaced_hi ^^^? (← (odd_spaced_hi <<<? (8 : i32)))))
      &&&? (16711935 : u32));
  let odd_spaced_hi : u32 ←
    ((← (odd_spaced_hi ^^^? (← (odd_spaced_hi <<<? (4 : i32)))))
      &&&? (252645135 : u32));
  let odd_spaced_hi : u32 ←
    ((← (odd_spaced_hi ^^^? (← (odd_spaced_hi <<<? (2 : i32)))))
      &&&? (858993459 : u32));
  let odd_spaced_hi : u32 ←
    ((← (odd_spaced_hi ^^^? (← (odd_spaced_hi <<<? (1 : i32)))))
      &&&? (1431655765 : u32));
  (pure (Lane2U32.mk
    (RustArray.ofVec #v[(← (even_spaced_lo
                            |||? (← (odd_spaced_lo <<<? (1 : i32))))),
                          (← (even_spaced_hi
                            |||? (← (odd_spaced_hi <<<? (1 : i32)))))])))

@[reducible] instance Impl_1.AssociatedTypes :
  core_models.ops.index.Index.AssociatedTypes Lane2U32 usize
  where
  Output := u32

instance Impl_1 : core_models.ops.index.Index Lane2U32 usize where
  index := fun (self : Lane2U32) (index : usize) => do
    (Lane2U32._0 self)[index]_?

@[spec]
def Impl.interleave (self : Lane2U32) : RustM Lane2U32 := do
  let lane_u64 : u64 ←
    ((← (libcrux_secrets.int.CastOps.as_u64 u32 (← self[(0 : usize)]_?)))
      |||? (← ((← (libcrux_secrets.int.CastOps.as_u64
          u32 (← self[(1 : usize)]_?)))
        <<<? (32 : i32))));
  let even_bits : u64 ← (lane_u64 &&&? (6148914691236517205 : u64));
  let even_bits : u64 ←
    ((← (even_bits ^^^? (← (even_bits >>>? (1 : i32)))))
      &&&? (3689348814741910323 : u64));
  let even_bits : u64 ←
    ((← (even_bits ^^^? (← (even_bits >>>? (2 : i32)))))
      &&&? (1085102592571150095 : u64));
  let even_bits : u64 ←
    ((← (even_bits ^^^? (← (even_bits >>>? (4 : i32)))))
      &&&? (71777214294589695 : u64));
  let even_bits : u64 ←
    ((← (even_bits ^^^? (← (even_bits >>>? (8 : i32)))))
      &&&? (281470681808895 : u64));
  let even_bits : u64 ←
    ((← (even_bits ^^^? (← (even_bits >>>? (16 : i32)))))
      &&&? (4294967295 : u64));
  let odd_bits : u64 ←
    ((← (lane_u64 >>>? (1 : i32))) &&&? (6148914691236517205 : u64));
  let odd_bits : u64 ←
    ((← (odd_bits ^^^? (← (odd_bits >>>? (1 : i32)))))
      &&&? (3689348814741910323 : u64));
  let odd_bits : u64 ←
    ((← (odd_bits ^^^? (← (odd_bits >>>? (2 : i32)))))
      &&&? (1085102592571150095 : u64));
  let odd_bits : u64 ←
    ((← (odd_bits ^^^? (← (odd_bits >>>? (4 : i32)))))
      &&&? (71777214294589695 : u64));
  let odd_bits : u64 ←
    ((← (odd_bits ^^^? (← (odd_bits >>>? (8 : i32)))))
      &&&? (281470681808895 : u64));
  let odd_bits : u64 ←
    ((← (odd_bits ^^^? (← (odd_bits >>>? (16 : i32)))))
      &&&? (4294967295 : u64));
  (Impl.from_ints
    (RustArray.ofVec #v[(← (libcrux_secrets.int.CastOps.as_u32 u64 even_bits)),
                          (← (libcrux_secrets.int.CastOps.as_u32
                            u64 odd_bits))]))

@[reducible] instance Impl_2.AssociatedTypes :
  core_models.convert.From.AssociatedTypes Lane2U32 (RustArray u32 2)
  where

instance Impl_2 : core_models.convert.From Lane2U32 (RustArray u32 2) where
  _from := fun (value : (RustArray u32 2)) => do (pure (Lane2U32.mk value))

@[instance] opaque Impl_5.AssociatedTypes :
  core_models.fmt.Debug.AssociatedTypes Lane2U32 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5 :
  core_models.fmt.Debug Lane2U32 :=
  by constructor <;> exact Inhabited.default

end libcrux_iot_sha3.lane


namespace libcrux_iot_sha3.state

structure KeccakState where
  st : (RustArray libcrux_iot_sha3.lane.Lane2U32 25)
  c : (RustArray libcrux_iot_sha3.lane.Lane2U32 5)
  d : (RustArray libcrux_iot_sha3.lane.Lane2U32 5)
  i : usize

end libcrux_iot_sha3.state


namespace libcrux_iot_sha3.keccak

--  The internal keccak state that can also buffer inputs to absorb.
--  This is used in the general xof APIs.
structure KeccakXofState (RATE : usize) where
  inner : libcrux_iot_sha3.state.KeccakState
  buf : (RustArray u8 RATE)
  buf_len : usize
  sponge : Bool

--  Consume the internal buffer and the required amount of the input to pad to
--  `RATE`.
-- 
--  Returns the `consumed` bytes from `inputs` if there's enough buffered
--  content to consume, and `0` otherwise.
--  If `consumed > 0` is returned, `self.buf` contains a full block to be
--  loaded.
@[spec]
def Impl.fill_buffer (RATE : usize)
    (self : (KeccakXofState (RATE)))
    (inputs : (RustSlice u8)) :
    RustM (rust_primitives.hax.Tuple2 (KeccakXofState (RATE)) usize) := do
  let input_len : usize ← (core_models.slice.Impl.len u8 inputs);
  let consumed : usize := (0 : usize);
  let ⟨consumed, self⟩ ←
    if (← ((KeccakXofState.buf_len self) >? (0 : usize))) then do
      if (← ((← ((KeccakXofState.buf_len self) +? input_len)) >=? RATE)) then do
        let consumed : usize ← (RATE -? (KeccakXofState.buf_len self));
        let self : (KeccakXofState (RATE)) :=
          {self
          with buf := (←
          (rust_primitives.hax.monomorphized_update_at.update_at_range_from
            (KeccakXofState.buf self)
            (core_models.ops.range.RangeFrom.mk
              (start := (KeccakXofState.buf_len self)))
            (← (core_models.slice.Impl.copy_from_slice u8
              (← (KeccakXofState.buf self)[
                (core_models.ops.range.RangeFrom.mk
                  (start := (KeccakXofState.buf_len self)))
                ]_?)
              (← inputs[
                (core_models.ops.range.RangeTo.mk (_end := consumed))
                ]_?)))))};
        let self : (KeccakXofState (RATE)) :=
          {self
          with buf_len := (← ((KeccakXofState.buf_len self) +? consumed))};
        (pure (rust_primitives.hax.Tuple2.mk consumed self))
      else do
        (pure (rust_primitives.hax.Tuple2.mk consumed self))
    else do
      (pure (rust_primitives.hax.Tuple2.mk consumed self));
  let hax_temp_output : usize := consumed;
  (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))

end libcrux_iot_sha3.keccak


namespace libcrux_iot_sha3.state

@[instance] opaque Impl_3.AssociatedTypes :
  core_models.fmt.Debug.AssociatedTypes KeccakState :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3 :
  core_models.fmt.Debug KeccakState :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1.AssociatedTypes :
  core_models.clone.Clone.AssociatedTypes KeccakState :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1 :
  core_models.clone.Clone KeccakState :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2.AssociatedTypes :
  core_models.marker.Copy.AssociatedTypes KeccakState :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2 :
  core_models.marker.Copy KeccakState :=
  by constructor <;> exact Inhabited.default

@[spec]
def Impl.new (_ : rust_primitives.hax.Tuple0) : RustM KeccakState := do
  (pure (KeccakState.mk
    (st := (← (rust_primitives.hax.repeat
      (← (libcrux_iot_sha3.lane.Impl.zero rust_primitives.hax.Tuple0.mk))
      (25 : usize))))
    (c := (← (rust_primitives.hax.repeat
      (← (libcrux_iot_sha3.lane.Impl.zero rust_primitives.hax.Tuple0.mk))
      (5 : usize))))
    (d := (← (rust_primitives.hax.repeat
      (← (libcrux_iot_sha3.lane.Impl.zero rust_primitives.hax.Tuple0.mk))
      (5 : usize))))
    (i := (0 : usize))))

end libcrux_iot_sha3.state


namespace libcrux_iot_sha3.keccak

--  Generate a new keccak xof state.
@[spec]
def Impl.new (RATE : usize) (_ : rust_primitives.hax.Tuple0) :
    RustM (KeccakXofState (RATE)) := do
  (pure (KeccakXofState.mk
    (inner := (← (libcrux_iot_sha3.state.Impl.new
      rust_primitives.hax.Tuple0.mk)))
    (buf := (← (Impl.zero_block (RATE) rust_primitives.hax.Tuple0.mk)))
    (buf_len := (0 : usize))
    (sponge := false)))

end libcrux_iot_sha3.keccak


namespace libcrux_iot_sha3.state

@[spec]
def Impl.get_with_zeta
    (self : KeccakState)
    (i : usize)
    (j : usize)
    (zeta : usize) :
    RustM u32 := do
  (← (KeccakState.st self)[(← ((← ((5 : usize) *? j)) +? i))]_?)[zeta]_?

end libcrux_iot_sha3.state


namespace libcrux_iot_sha3.keccak

set_option maxRecDepth 1000 in

@[spec]
def keccakf1600_round0_theta (s : libcrux_iot_sha3.state.KeccakState) :
    RustM libcrux_iot_sha3.state.KeccakState := do
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (0 : usize)
      (0 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (0 : usize)
      (0 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (0 : usize)
      (0 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (0 : usize)
      (0 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (0 : usize)
      (0 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (0 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(0 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(0 : usize)]_?))
        (0 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (0 : usize)
      (1 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (0 : usize)
      (1 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (0 : usize)
      (1 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (0 : usize)
      (1 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (0 : usize)
      (1 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (0 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(0 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(0 : usize)]_?))
        (1 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (1 : usize)
      (0 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (1 : usize)
      (0 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (1 : usize)
      (0 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (1 : usize)
      (0 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (1 : usize)
      (0 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (1 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(1 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(1 : usize)]_?))
        (0 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (1 : usize)
      (1 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (1 : usize)
      (1 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (1 : usize)
      (1 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (1 : usize)
      (1 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (1 : usize)
      (1 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (1 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(1 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(1 : usize)]_?))
        (1 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (2 : usize)
      (0 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (2 : usize)
      (0 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (2 : usize)
      (0 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (2 : usize)
      (0 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (2 : usize)
      (0 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (2 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(2 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(2 : usize)]_?))
        (0 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (2 : usize)
      (1 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (2 : usize)
      (1 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (2 : usize)
      (1 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (2 : usize)
      (1 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (2 : usize)
      (1 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (2 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(2 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(2 : usize)]_?))
        (1 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (3 : usize)
      (0 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (3 : usize)
      (0 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (3 : usize)
      (0 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (3 : usize)
      (0 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (3 : usize)
      (0 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (3 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(3 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(3 : usize)]_?))
        (0 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (3 : usize)
      (1 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (3 : usize)
      (1 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (3 : usize)
      (1 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (3 : usize)
      (1 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (3 : usize)
      (1 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (3 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(3 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(3 : usize)]_?))
        (1 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (4 : usize)
      (0 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (4 : usize)
      (0 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (4 : usize)
      (0 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (4 : usize)
      (0 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (4 : usize)
      (0 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (4 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(4 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(4 : usize)]_?))
        (0 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (4 : usize)
      (1 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (4 : usize)
      (1 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (4 : usize)
      (1 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (4 : usize)
      (1 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (4 : usize)
      (1 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (4 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(4 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(4 : usize)]_?))
        (1 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let c_x4_zeta0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(4 : usize)]_?)[(0 : usize)]_?;
  let c_x1_zeta1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(1 : usize)]_?)[(1 : usize)]_?;
  let c_x3_zeta0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(3 : usize)]_?)[(0 : usize)]_?;
  let c_x0_zeta1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(0 : usize)]_?)[(1 : usize)]_?;
  let c_x2_zeta0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(2 : usize)]_?)[(0 : usize)]_?;
  let c_x4_zeta1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(4 : usize)]_?)[(1 : usize)]_?;
  let d_x0_zeta0 : u32 ←
    (c_x4_zeta0
      ^^^? (← (core_models.num.Impl_8.rotate_left c_x1_zeta1 (1 : u32))));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (0 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?))
        (0 : usize)
        d_x0_zeta0))}))};
  let d_x2_zeta1 : u32 ← (c_x1_zeta1 ^^^? c_x3_zeta0);
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (2 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?))
        (1 : usize)
        d_x2_zeta1))}))};
  let d_x4_zeta0 : u32 ←
    (c_x3_zeta0
      ^^^? (← (core_models.num.Impl_8.rotate_left c_x0_zeta1 (1 : u32))));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (4 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?))
        (0 : usize)
        d_x4_zeta0))}))};
  let d_x1_zeta1 : u32 ← (c_x0_zeta1 ^^^? c_x2_zeta0);
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (1 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?))
        (1 : usize)
        d_x1_zeta1))}))};
  let d_x3_zeta0 : u32 ←
    (c_x2_zeta0
      ^^^? (← (core_models.num.Impl_8.rotate_left c_x4_zeta1 (1 : u32))));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (3 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?))
        (0 : usize)
        d_x3_zeta0))}))};
  let c_x1_zeta0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(1 : usize)]_?)[(0 : usize)]_?;
  let c_x3_zeta1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(3 : usize)]_?)[(1 : usize)]_?;
  let c_x2_zeta1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(2 : usize)]_?)[(1 : usize)]_?;
  let c_x0_zeta0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(0 : usize)]_?)[(0 : usize)]_?;
  let d_x0_zeta1 : u32 ← (c_x4_zeta1 ^^^? c_x1_zeta0);
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (0 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?))
        (1 : usize)
        d_x0_zeta1))}))};
  let d_x2_zeta0 : u32 ←
    (c_x1_zeta0
      ^^^? (← (core_models.num.Impl_8.rotate_left c_x3_zeta1 (1 : u32))));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (2 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?))
        (0 : usize)
        d_x2_zeta0))}))};
  let d_x4_zeta1 : u32 ← (c_x3_zeta1 ^^^? c_x0_zeta0);
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (4 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?))
        (1 : usize)
        d_x4_zeta1))}))};
  let d_x1_zeta0 : u32 ←
    (c_x0_zeta0
      ^^^? (← (core_models.num.Impl_8.rotate_left c_x2_zeta1 (1 : u32))));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (1 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?))
        (0 : usize)
        d_x1_zeta0))}))};
  let d_x3_zeta1 : u32 ← (c_x2_zeta1 ^^^? c_x4_zeta0);
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (3 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?))
        (1 : usize)
        d_x3_zeta1))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure s)

set_option maxRecDepth 1000 in

@[spec]
def keccakf1600_round1_theta (s : libcrux_iot_sha3.state.KeccakState) :
    RustM libcrux_iot_sha3.state.KeccakState := do
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (0 : usize)
      (0 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (0 : usize)
      (1 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (0 : usize)
      (0 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (0 : usize)
      (0 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (0 : usize)
      (1 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (0 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(0 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(0 : usize)]_?))
        (0 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (0 : usize)
      (1 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (0 : usize)
      (0 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (0 : usize)
      (1 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (0 : usize)
      (1 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (0 : usize)
      (0 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (0 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(0 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(0 : usize)]_?))
        (1 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (1 : usize)
      (0 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (1 : usize)
      (1 : usize));
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (1 : usize)
      (1 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (1 : usize)
      (0 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (1 : usize)
      (0 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (1 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(1 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(1 : usize)]_?))
        (0 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (1 : usize)
      (1 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (1 : usize)
      (0 : usize));
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (1 : usize)
      (0 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (1 : usize)
      (1 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (1 : usize)
      (1 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (1 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(1 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(1 : usize)]_?))
        (1 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (2 : usize)
      (1 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (2 : usize)
      (1 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (2 : usize)
      (0 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (2 : usize)
      (1 : usize));
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (2 : usize)
      (0 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (2 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(2 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(2 : usize)]_?))
        (0 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (2 : usize)
      (0 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (2 : usize)
      (0 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (2 : usize)
      (1 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (2 : usize)
      (0 : usize));
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (2 : usize)
      (1 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (2 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(2 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(2 : usize)]_?))
        (1 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (3 : usize)
      (1 : usize));
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (3 : usize)
      (0 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (3 : usize)
      (1 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (3 : usize)
      (0 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (3 : usize)
      (1 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (3 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(3 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(3 : usize)]_?))
        (0 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (3 : usize)
      (0 : usize));
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (3 : usize)
      (1 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (3 : usize)
      (0 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (3 : usize)
      (1 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (3 : usize)
      (0 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (3 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(3 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(3 : usize)]_?))
        (1 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (4 : usize)
      (0 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (4 : usize)
      (0 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (4 : usize)
      (0 : usize));
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (4 : usize)
      (1 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (4 : usize)
      (1 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (4 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(4 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(4 : usize)]_?))
        (0 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (4 : usize)
      (1 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (4 : usize)
      (1 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (4 : usize)
      (1 : usize));
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (4 : usize)
      (0 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (4 : usize)
      (0 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (4 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(4 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(4 : usize)]_?))
        (1 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let c_x4_zeta0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(4 : usize)]_?)[(0 : usize)]_?;
  let c_x1_zeta1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(1 : usize)]_?)[(1 : usize)]_?;
  let c_x3_zeta0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(3 : usize)]_?)[(0 : usize)]_?;
  let c_x0_zeta1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(0 : usize)]_?)[(1 : usize)]_?;
  let c_x2_zeta0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(2 : usize)]_?)[(0 : usize)]_?;
  let c_x4_zeta1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(4 : usize)]_?)[(1 : usize)]_?;
  let d_x0_zeta0 : u32 ←
    (c_x4_zeta0
      ^^^? (← (core_models.num.Impl_8.rotate_left c_x1_zeta1 (1 : u32))));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (0 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?))
        (0 : usize)
        d_x0_zeta0))}))};
  let d_x2_zeta1 : u32 ← (c_x1_zeta1 ^^^? c_x3_zeta0);
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (2 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?))
        (1 : usize)
        d_x2_zeta1))}))};
  let d_x4_zeta0 : u32 ←
    (c_x3_zeta0
      ^^^? (← (core_models.num.Impl_8.rotate_left c_x0_zeta1 (1 : u32))));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (4 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?))
        (0 : usize)
        d_x4_zeta0))}))};
  let d_x1_zeta1 : u32 ← (c_x0_zeta1 ^^^? c_x2_zeta0);
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (1 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?))
        (1 : usize)
        d_x1_zeta1))}))};
  let d_x3_zeta0 : u32 ←
    (c_x2_zeta0
      ^^^? (← (core_models.num.Impl_8.rotate_left c_x4_zeta1 (1 : u32))));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (3 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?))
        (0 : usize)
        d_x3_zeta0))}))};
  let c_x1_zeta0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(1 : usize)]_?)[(0 : usize)]_?;
  let c_x3_zeta1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(3 : usize)]_?)[(1 : usize)]_?;
  let c_x2_zeta1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(2 : usize)]_?)[(1 : usize)]_?;
  let c_x0_zeta0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(0 : usize)]_?)[(0 : usize)]_?;
  let d_x0_zeta1 : u32 ← (c_x4_zeta1 ^^^? c_x1_zeta0);
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (0 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?))
        (1 : usize)
        d_x0_zeta1))}))};
  let d_x2_zeta0 : u32 ←
    (c_x1_zeta0
      ^^^? (← (core_models.num.Impl_8.rotate_left c_x3_zeta1 (1 : u32))));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (2 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?))
        (0 : usize)
        d_x2_zeta0))}))};
  let d_x4_zeta1 : u32 ← (c_x3_zeta1 ^^^? c_x0_zeta0);
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (4 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?))
        (1 : usize)
        d_x4_zeta1))}))};
  let d_x1_zeta0 : u32 ←
    (c_x0_zeta0
      ^^^? (← (core_models.num.Impl_8.rotate_left c_x2_zeta1 (1 : u32))));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (1 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?))
        (0 : usize)
        d_x1_zeta0))}))};
  let d_x3_zeta1 : u32 ← (c_x2_zeta1 ^^^? c_x4_zeta0);
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (3 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?))
        (1 : usize)
        d_x3_zeta1))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure s)

set_option maxRecDepth 1000 in

@[spec]
def keccakf1600_round2_theta (s : libcrux_iot_sha3.state.KeccakState) :
    RustM libcrux_iot_sha3.state.KeccakState := do
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (0 : usize)
      (0 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (0 : usize)
      (1 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (0 : usize)
      (1 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (0 : usize)
      (1 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (0 : usize)
      (1 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (0 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(0 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(0 : usize)]_?))
        (0 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (0 : usize)
      (1 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (0 : usize)
      (0 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (0 : usize)
      (0 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (0 : usize)
      (0 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (0 : usize)
      (0 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (0 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(0 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(0 : usize)]_?))
        (1 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (1 : usize)
      (1 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (1 : usize)
      (1 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (1 : usize)
      (1 : usize));
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (1 : usize)
      (1 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (1 : usize)
      (0 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (1 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(1 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(1 : usize)]_?))
        (0 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (1 : usize)
      (0 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (1 : usize)
      (0 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (1 : usize)
      (0 : usize));
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (1 : usize)
      (0 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (1 : usize)
      (1 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (1 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(1 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(1 : usize)]_?))
        (1 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (2 : usize)
      (1 : usize));
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (2 : usize)
      (1 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (2 : usize)
      (1 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (2 : usize)
      (0 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (2 : usize)
      (1 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (2 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(2 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(2 : usize)]_?))
        (0 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (2 : usize)
      (0 : usize));
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (2 : usize)
      (0 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (2 : usize)
      (0 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (2 : usize)
      (1 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (2 : usize)
      (0 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (2 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(2 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(2 : usize)]_?))
        (1 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (3 : usize)
      (1 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (3 : usize)
      (1 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (3 : usize)
      (0 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (3 : usize)
      (1 : usize));
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (3 : usize)
      (1 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (3 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(3 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(3 : usize)]_?))
        (0 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (3 : usize)
      (0 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (3 : usize)
      (0 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (3 : usize)
      (1 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (3 : usize)
      (0 : usize));
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (3 : usize)
      (0 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (3 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(3 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(3 : usize)]_?))
        (1 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (4 : usize)
      (1 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (4 : usize)
      (0 : usize));
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (4 : usize)
      (1 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (4 : usize)
      (1 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (4 : usize)
      (1 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (4 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(4 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(4 : usize)]_?))
        (0 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (4 : usize)
      (0 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (4 : usize)
      (1 : usize));
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (4 : usize)
      (0 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (4 : usize)
      (0 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (4 : usize)
      (0 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (4 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(4 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(4 : usize)]_?))
        (1 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let c_x4_zeta0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(4 : usize)]_?)[(0 : usize)]_?;
  let c_x1_zeta1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(1 : usize)]_?)[(1 : usize)]_?;
  let c_x3_zeta0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(3 : usize)]_?)[(0 : usize)]_?;
  let c_x0_zeta1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(0 : usize)]_?)[(1 : usize)]_?;
  let c_x2_zeta0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(2 : usize)]_?)[(0 : usize)]_?;
  let c_x4_zeta1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(4 : usize)]_?)[(1 : usize)]_?;
  let d_x0_zeta0 : u32 ←
    (c_x4_zeta0
      ^^^? (← (core_models.num.Impl_8.rotate_left c_x1_zeta1 (1 : u32))));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (0 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?))
        (0 : usize)
        d_x0_zeta0))}))};
  let d_x2_zeta1 : u32 ← (c_x1_zeta1 ^^^? c_x3_zeta0);
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (2 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?))
        (1 : usize)
        d_x2_zeta1))}))};
  let d_x4_zeta0 : u32 ←
    (c_x3_zeta0
      ^^^? (← (core_models.num.Impl_8.rotate_left c_x0_zeta1 (1 : u32))));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (4 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?))
        (0 : usize)
        d_x4_zeta0))}))};
  let d_x1_zeta1 : u32 ← (c_x0_zeta1 ^^^? c_x2_zeta0);
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (1 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?))
        (1 : usize)
        d_x1_zeta1))}))};
  let d_x3_zeta0 : u32 ←
    (c_x2_zeta0
      ^^^? (← (core_models.num.Impl_8.rotate_left c_x4_zeta1 (1 : u32))));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (3 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?))
        (0 : usize)
        d_x3_zeta0))}))};
  let c_x1_zeta0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(1 : usize)]_?)[(0 : usize)]_?;
  let c_x3_zeta1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(3 : usize)]_?)[(1 : usize)]_?;
  let c_x2_zeta1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(2 : usize)]_?)[(1 : usize)]_?;
  let c_x0_zeta0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(0 : usize)]_?)[(0 : usize)]_?;
  let d_x0_zeta1 : u32 ← (c_x4_zeta1 ^^^? c_x1_zeta0);
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (0 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?))
        (1 : usize)
        d_x0_zeta1))}))};
  let d_x2_zeta0 : u32 ←
    (c_x1_zeta0
      ^^^? (← (core_models.num.Impl_8.rotate_left c_x3_zeta1 (1 : u32))));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (2 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?))
        (0 : usize)
        d_x2_zeta0))}))};
  let d_x4_zeta1 : u32 ← (c_x3_zeta1 ^^^? c_x0_zeta0);
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (4 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?))
        (1 : usize)
        d_x4_zeta1))}))};
  let d_x1_zeta0 : u32 ←
    (c_x0_zeta0
      ^^^? (← (core_models.num.Impl_8.rotate_left c_x2_zeta1 (1 : u32))));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (1 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?))
        (0 : usize)
        d_x1_zeta0))}))};
  let d_x3_zeta1 : u32 ← (c_x2_zeta1 ^^^? c_x4_zeta0);
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (3 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?))
        (1 : usize)
        d_x3_zeta1))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure s)

set_option maxRecDepth 1000 in

@[spec]
def keccakf1600_round3_theta (s : libcrux_iot_sha3.state.KeccakState) :
    RustM libcrux_iot_sha3.state.KeccakState := do
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (0 : usize)
      (0 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (0 : usize)
      (0 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (0 : usize)
      (1 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (0 : usize)
      (1 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (0 : usize)
      (0 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (0 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(0 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(0 : usize)]_?))
        (0 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (0 : usize)
      (1 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (0 : usize)
      (1 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (0 : usize)
      (0 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (0 : usize)
      (0 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (0 : usize)
      (1 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (0 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(0 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(0 : usize)]_?))
        (1 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (1 : usize)
      (1 : usize));
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (1 : usize)
      (0 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (1 : usize)
      (0 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (1 : usize)
      (1 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (1 : usize)
      (0 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (1 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(1 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(1 : usize)]_?))
        (0 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (1 : usize)
      (0 : usize));
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (1 : usize)
      (1 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (1 : usize)
      (1 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (1 : usize)
      (0 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (1 : usize)
      (1 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (1 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(1 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(1 : usize)]_?))
        (1 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (2 : usize)
      (0 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (2 : usize)
      (0 : usize));
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (2 : usize)
      (1 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (2 : usize)
      (1 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (2 : usize)
      (1 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (2 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(2 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(2 : usize)]_?))
        (0 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (2 : usize)
      (1 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (2 : usize)
      (1 : usize));
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (2 : usize)
      (0 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (2 : usize)
      (0 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (2 : usize)
      (0 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (2 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(2 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(2 : usize)]_?))
        (1 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (3 : usize)
      (0 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (3 : usize)
      (1 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (3 : usize)
      (1 : usize));
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (3 : usize)
      (1 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (3 : usize)
      (0 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (3 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(3 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(3 : usize)]_?))
        (0 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (3 : usize)
      (1 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (3 : usize)
      (0 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (3 : usize)
      (0 : usize));
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (3 : usize)
      (0 : usize));
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (3 : usize)
      (1 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (3 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(3 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(3 : usize)]_?))
        (1 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (4 : usize)
      (1 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (4 : usize)
      (0 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (4 : usize)
      (1 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (4 : usize)
      (0 : usize));
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (4 : usize)
      (0 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (4 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(4 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(4 : usize)]_?))
        (0 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let ax_3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (4 : usize)
      (0 : usize));
  let ax_1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (4 : usize)
      (1 : usize));
  let ax_4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (4 : usize)
      (0 : usize));
  let ax_2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (4 : usize)
      (1 : usize));
  let ax_0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (4 : usize)
      (1 : usize));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with c := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.c s)
      (4 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.c s)[(4 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.c s)[(4 : usize)]_?))
        (1 : usize)
        (← ((← ((← ((← (ax_0 ^^^? ax_1)) ^^^? ax_2)) ^^^? ax_3))
          ^^^? ax_4))))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let c_x4_zeta0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(4 : usize)]_?)[(0 : usize)]_?;
  let c_x1_zeta1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(1 : usize)]_?)[(1 : usize)]_?;
  let c_x3_zeta0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(3 : usize)]_?)[(0 : usize)]_?;
  let c_x0_zeta1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(0 : usize)]_?)[(1 : usize)]_?;
  let c_x2_zeta0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(2 : usize)]_?)[(0 : usize)]_?;
  let c_x4_zeta1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(4 : usize)]_?)[(1 : usize)]_?;
  let d_x0_zeta0 : u32 ←
    (c_x4_zeta0
      ^^^? (← (core_models.num.Impl_8.rotate_left c_x1_zeta1 (1 : u32))));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (0 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?))
        (0 : usize)
        d_x0_zeta0))}))};
  let d_x2_zeta1 : u32 ← (c_x1_zeta1 ^^^? c_x3_zeta0);
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (2 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?))
        (1 : usize)
        d_x2_zeta1))}))};
  let d_x4_zeta0 : u32 ←
    (c_x3_zeta0
      ^^^? (← (core_models.num.Impl_8.rotate_left c_x0_zeta1 (1 : u32))));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (4 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?))
        (0 : usize)
        d_x4_zeta0))}))};
  let d_x1_zeta1 : u32 ← (c_x0_zeta1 ^^^? c_x2_zeta0);
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (1 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?))
        (1 : usize)
        d_x1_zeta1))}))};
  let d_x3_zeta0 : u32 ←
    (c_x2_zeta0
      ^^^? (← (core_models.num.Impl_8.rotate_left c_x4_zeta1 (1 : u32))));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (3 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?))
        (0 : usize)
        d_x3_zeta0))}))};
  let c_x1_zeta0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(1 : usize)]_?)[(0 : usize)]_?;
  let c_x3_zeta1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(3 : usize)]_?)[(1 : usize)]_?;
  let c_x2_zeta1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(2 : usize)]_?)[(1 : usize)]_?;
  let c_x0_zeta0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.c s)[(0 : usize)]_?)[(0 : usize)]_?;
  let d_x0_zeta1 : u32 ← (c_x4_zeta1 ^^^? c_x1_zeta0);
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (0 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?))
        (1 : usize)
        d_x0_zeta1))}))};
  let d_x2_zeta0 : u32 ←
    (c_x1_zeta0
      ^^^? (← (core_models.num.Impl_8.rotate_left c_x3_zeta1 (1 : u32))));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (2 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?))
        (0 : usize)
        d_x2_zeta0))}))};
  let d_x4_zeta1 : u32 ← (c_x3_zeta1 ^^^? c_x0_zeta0);
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (4 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?))
        (1 : usize)
        d_x4_zeta1))}))};
  let d_x1_zeta0 : u32 ←
    (c_x0_zeta0
      ^^^? (← (core_models.num.Impl_8.rotate_left c_x2_zeta1 (1 : u32))));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (1 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?))
        (0 : usize)
        d_x1_zeta0))}))};
  let d_x3_zeta1 : u32 ← (c_x2_zeta1 ^^^? c_x4_zeta0);
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s
    with d := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (libcrux_iot_sha3.state.KeccakState.d s)
      (3 : usize)
      {(← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?))
        (1 : usize)
        d_x3_zeta1))}))};
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure s)

end libcrux_iot_sha3.keccak


namespace libcrux_iot_sha3.state

@[spec]
def Impl.set_with_zeta
    (self : KeccakState)
    (i : usize)
    (j : usize)
    (zeta : usize)
    (v : u32) :
    RustM KeccakState := do
  let self : KeccakState :=
    {self
    with st := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (KeccakState.st self)
      (← ((← ((5 : usize) *? j)) +? i))
      {(← (KeccakState.st self)[(← ((← ((5 : usize) *? j)) +? i))]_?)
      with _0 := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
        (libcrux_iot_sha3.lane.Lane2U32._0
          (← (KeccakState.st self)[(← ((← ((5 : usize) *? j)) +? i))]_?))
        zeta
        v))}))};
  (pure self)

end libcrux_iot_sha3.state


namespace libcrux_iot_sha3.keccak

set_option maxRecDepth 1000 in

@[spec]
def keccakf1600_round0_pi_rho_chi_1 (BASE_ROUND : usize)
    (s : libcrux_iot_sha3.state.KeccakState) :
    RustM libcrux_iot_sha3.state.KeccakState := do
  let i : usize := (libcrux_iot_sha3.state.KeccakState.i s);
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (0 : usize)
      (0 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(0 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (1 : usize)
      (0 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx0, bx1⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (0 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (22 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (2 : usize)
      (1 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(1 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (3 : usize)
      (1 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(1 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (4 : usize)
      (0 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx2, bx3, bx4⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (22 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (11 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (7 : u32))));
  let ax0 : u32 := (0 : u32);
  let ax0 : u32 ←
    ((← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)))) ^^^? (← RC_INTERLEAVED_0[i]_?));
  let _ := rust_primitives.hax.Tuple0.mk;
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (0 : usize)
      (0 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (1 : usize)
      (0 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (2 : usize)
      (1 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (3 : usize)
      (1 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (4 : usize)
      (0 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (0 : usize)
      (1 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(1 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (1 : usize)
      (1 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx0, bx1⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (0 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (22 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (2 : usize)
      (0 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(0 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (3 : usize)
      (0 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(0 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (4 : usize)
      (1 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx2, bx3, bx4⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (21 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (10 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (7 : u32))));
  let ax0 : u32 := (0 : u32);
  let ax0 : u32 ←
    ((← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)))) ^^^? (← RC_INTERLEAVED_1[i]_?));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s with i := (← (i +? (1 : usize)))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (0 : usize)
      (1 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (1 : usize)
      (1 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (2 : usize)
      (0 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (3 : usize)
      (0 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (4 : usize)
      (1 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (0 : usize)
      (1 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(1 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (1 : usize)
      (1 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx2, bx3⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (2 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (23 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (2 : usize)
      (1 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(1 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (3 : usize)
      (0 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(0 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (4 : usize)
      (0 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx4, bx0, bx1⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (31 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (14 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (10 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (0 : usize)
      (1 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (1 : usize)
      (1 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (2 : usize)
      (1 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (3 : usize)
      (0 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (4 : usize)
      (0 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (0 : usize)
      (0 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(0 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (1 : usize)
      (0 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx2, bx3⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (1 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (22 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (2 : usize)
      (0 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(0 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (3 : usize)
      (1 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(1 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (4 : usize)
      (1 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx4, bx0, bx1⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (30 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (14 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (10 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (0 : usize)
      (0 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (1 : usize)
      (0 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (2 : usize)
      (0 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (3 : usize)
      (1 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (4 : usize)
      (1 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure s)

set_option maxRecDepth 1500 in

@[spec]
def keccakf1600_round0_pi_rho_chi_2 (s : libcrux_iot_sha3.state.KeccakState) :
    RustM libcrux_iot_sha3.state.KeccakState := do
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (0 : usize)
      (0 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(0 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (1 : usize)
      (1 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx4, bx0⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (9 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (1 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (2 : usize)
      (0 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(0 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (3 : usize)
      (1 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(1 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (4 : usize)
      (0 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx1, bx2, bx3⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (3 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (13 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (4 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (0 : usize)
      (0 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (1 : usize)
      (1 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (2 : usize)
      (0 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (3 : usize)
      (1 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (4 : usize)
      (0 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (0 : usize)
      (1 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(1 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (1 : usize)
      (0 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx4, bx0⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (9 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (0 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (2 : usize)
      (1 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(1 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (3 : usize)
      (0 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(0 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (4 : usize)
      (1 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx1, bx2, bx3⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (3 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (12 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (4 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (0 : usize)
      (1 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (1 : usize)
      (0 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (2 : usize)
      (1 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (3 : usize)
      (0 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (4 : usize)
      (1 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (0 : usize)
      (0 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(0 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (1 : usize)
      (0 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx1, bx2⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (18 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (5 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (2 : usize)
      (1 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(1 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (3 : usize)
      (0 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(0 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (4 : usize)
      (1 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx3, bx4, bx0⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (8 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (28 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (14 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (0 : usize)
      (0 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (1 : usize)
      (0 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (2 : usize)
      (1 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (3 : usize)
      (0 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (4 : usize)
      (1 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (0 : usize)
      (1 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(1 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (1 : usize)
      (1 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx1, bx2⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (18 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (5 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (2 : usize)
      (0 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(0 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (3 : usize)
      (1 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(1 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (4 : usize)
      (0 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx3, bx4, bx0⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (7 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (28 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (13 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (0 : usize)
      (1 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (1 : usize)
      (1 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (2 : usize)
      (0 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (3 : usize)
      (1 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (4 : usize)
      (0 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (0 : usize)
      (1 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(1 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (1 : usize)
      (0 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx3, bx4⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (21 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (1 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (2 : usize)
      (0 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(0 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (3 : usize)
      (1 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(1 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (4 : usize)
      (1 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx0, bx1, bx2⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (31 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (28 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (20 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (0 : usize)
      (1 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (1 : usize)
      (0 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (2 : usize)
      (0 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (3 : usize)
      (1 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (4 : usize)
      (1 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (0 : usize)
      (0 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(0 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (1 : usize)
      (1 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx3, bx4⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (20 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (1 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (2 : usize)
      (1 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(1 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (3 : usize)
      (0 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(0 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (4 : usize)
      (0 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx0, bx1, bx2⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (31 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (27 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (19 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (0 : usize)
      (0 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (1 : usize)
      (1 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (2 : usize)
      (1 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (3 : usize)
      (0 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (4 : usize)
      (0 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure s)

set_option maxRecDepth 1000 in

@[spec]
def keccakf1600_round1_pi_rho_chi_1 (BASE_ROUND : usize)
    (s : libcrux_iot_sha3.state.KeccakState) :
    RustM libcrux_iot_sha3.state.KeccakState := do
  let i : usize := (libcrux_iot_sha3.state.KeccakState.i s);
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (0 : usize)
      (0 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(0 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (1 : usize)
      (1 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx0, bx1⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (0 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (22 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (2 : usize)
      (1 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(1 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (3 : usize)
      (1 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(1 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (4 : usize)
      (1 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx2, bx3, bx4⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (22 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (11 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (7 : u32))));
  let ax0 : u32 := (0 : u32);
  let ax0 : u32 ←
    ((← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)))) ^^^? (← RC_INTERLEAVED_0[i]_?));
  let _ := rust_primitives.hax.Tuple0.mk;
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (0 : usize)
      (0 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (1 : usize)
      (1 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (2 : usize)
      (1 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (3 : usize)
      (1 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (4 : usize)
      (1 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (0 : usize)
      (1 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(1 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (1 : usize)
      (0 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx0, bx1⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (0 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (22 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (2 : usize)
      (0 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(0 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (3 : usize)
      (0 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(0 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (4 : usize)
      (0 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx2, bx3, bx4⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (21 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (10 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (7 : u32))));
  let ax0 : u32 := (0 : u32);
  let ax0 : u32 ←
    ((← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)))) ^^^? (← RC_INTERLEAVED_1[i]_?));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s with i := (← (i +? (1 : usize)))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (0 : usize)
      (1 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (1 : usize)
      (0 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (2 : usize)
      (0 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (3 : usize)
      (0 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (4 : usize)
      (0 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (0 : usize)
      (1 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(1 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (1 : usize)
      (1 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx2, bx3⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (2 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (23 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (2 : usize)
      (1 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(1 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (3 : usize)
      (1 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(0 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (4 : usize)
      (0 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx4, bx0, bx1⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (31 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (14 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (10 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (0 : usize)
      (1 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (1 : usize)
      (1 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (2 : usize)
      (1 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (3 : usize)
      (1 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (4 : usize)
      (0 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (0 : usize)
      (0 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(0 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (1 : usize)
      (0 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx2, bx3⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (1 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (22 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (2 : usize)
      (0 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(0 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (3 : usize)
      (0 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(1 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (4 : usize)
      (1 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx4, bx0, bx1⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (30 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (14 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (10 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (0 : usize)
      (0 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (1 : usize)
      (0 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (2 : usize)
      (0 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (3 : usize)
      (0 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (4 : usize)
      (1 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure s)

set_option maxRecDepth 1500 in

@[spec]
def keccakf1600_round1_pi_rho_chi_2 (s : libcrux_iot_sha3.state.KeccakState) :
    RustM libcrux_iot_sha3.state.KeccakState := do
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (0 : usize)
      (1 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(0 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (1 : usize)
      (1 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx4, bx0⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (9 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (1 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (2 : usize)
      (1 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(0 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (3 : usize)
      (0 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(1 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (4 : usize)
      (1 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx1, bx2, bx3⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (3 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (13 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (4 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (0 : usize)
      (1 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (1 : usize)
      (1 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (2 : usize)
      (1 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (3 : usize)
      (0 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (4 : usize)
      (1 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (0 : usize)
      (0 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(1 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (1 : usize)
      (0 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx4, bx0⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (9 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (0 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (2 : usize)
      (0 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(1 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (3 : usize)
      (1 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(0 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (4 : usize)
      (0 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx1, bx2, bx3⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (3 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (12 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (4 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (0 : usize)
      (0 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (1 : usize)
      (0 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (2 : usize)
      (0 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (3 : usize)
      (1 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (4 : usize)
      (0 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (0 : usize)
      (1 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(0 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (1 : usize)
      (1 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx1, bx2⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (18 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (5 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (2 : usize)
      (0 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(1 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (3 : usize)
      (1 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(0 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (4 : usize)
      (1 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx3, bx4, bx0⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (8 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (28 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (14 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (0 : usize)
      (1 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (1 : usize)
      (1 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (2 : usize)
      (0 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (3 : usize)
      (1 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (4 : usize)
      (1 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (0 : usize)
      (0 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(1 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (1 : usize)
      (0 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx1, bx2⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (18 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (5 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (2 : usize)
      (1 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(0 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (3 : usize)
      (0 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(1 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (4 : usize)
      (0 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx3, bx4, bx0⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (7 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (28 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (13 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (0 : usize)
      (0 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (1 : usize)
      (0 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (2 : usize)
      (1 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (3 : usize)
      (0 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (4 : usize)
      (0 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (0 : usize)
      (1 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(1 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (1 : usize)
      (0 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx3, bx4⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (21 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (1 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (2 : usize)
      (1 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(0 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (3 : usize)
      (1 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(1 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (4 : usize)
      (1 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx0, bx1, bx2⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (31 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (28 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (20 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (0 : usize)
      (1 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (1 : usize)
      (0 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (2 : usize)
      (1 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (3 : usize)
      (1 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (4 : usize)
      (1 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (0 : usize)
      (0 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(0 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (1 : usize)
      (1 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx3, bx4⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (20 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (1 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (2 : usize)
      (0 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(1 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (3 : usize)
      (0 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(0 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (4 : usize)
      (0 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx0, bx1, bx2⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (31 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (27 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (19 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (0 : usize)
      (0 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (1 : usize)
      (1 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (2 : usize)
      (0 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (3 : usize)
      (0 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (4 : usize)
      (0 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure s)

set_option maxRecDepth 1000 in

@[spec]
def keccakf1600_round2_pi_rho_chi_1 (BASE_ROUND : usize)
    (s : libcrux_iot_sha3.state.KeccakState) :
    RustM libcrux_iot_sha3.state.KeccakState := do
  let i : usize := (libcrux_iot_sha3.state.KeccakState.i s);
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (0 : usize)
      (0 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(0 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (1 : usize)
      (1 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx0, bx1⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (0 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (22 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (2 : usize)
      (0 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(1 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (3 : usize)
      (0 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(1 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (4 : usize)
      (1 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx2, bx3, bx4⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (22 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (11 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (7 : u32))));
  let ax0 : u32 := (0 : u32);
  let ax0 : u32 ←
    ((← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)))) ^^^? (← RC_INTERLEAVED_0[i]_?));
  let _ := rust_primitives.hax.Tuple0.mk;
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (0 : usize)
      (0 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (1 : usize)
      (1 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (2 : usize)
      (0 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (3 : usize)
      (0 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (4 : usize)
      (1 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (0 : usize)
      (1 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(1 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (1 : usize)
      (0 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx0, bx1⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (0 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (22 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (2 : usize)
      (1 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(0 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (3 : usize)
      (1 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(0 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (4 : usize)
      (0 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx2, bx3, bx4⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (21 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (10 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (7 : u32))));
  let ax0 : u32 := (0 : u32);
  let ax0 : u32 ←
    ((← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)))) ^^^? (← RC_INTERLEAVED_1[i]_?));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s with i := (← (i +? (1 : usize)))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (0 : usize)
      (1 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (1 : usize)
      (0 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (2 : usize)
      (1 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (3 : usize)
      (1 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (4 : usize)
      (0 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (0 : usize)
      (0 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(1 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (1 : usize)
      (0 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx2, bx3⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (2 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (23 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (2 : usize)
      (0 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(1 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (3 : usize)
      (1 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(0 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (4 : usize)
      (0 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx4, bx0, bx1⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (31 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (14 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (10 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (0 : usize)
      (0 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (1 : usize)
      (0 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (2 : usize)
      (0 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (3 : usize)
      (1 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (4 : usize)
      (0 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (0 : usize)
      (1 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(0 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (1 : usize)
      (1 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx2, bx3⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (1 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (22 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (2 : usize)
      (1 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(0 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (3 : usize)
      (0 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(1 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (4 : usize)
      (1 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx4, bx0, bx1⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (30 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (14 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (10 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (0 : usize)
      (1 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (1 : usize)
      (1 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (2 : usize)
      (1 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (3 : usize)
      (0 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (4 : usize)
      (1 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure s)

set_option maxRecDepth 1500 in

@[spec]
def keccakf1600_round2_pi_rho_chi_2 (s : libcrux_iot_sha3.state.KeccakState) :
    RustM libcrux_iot_sha3.state.KeccakState := do
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (0 : usize)
      (1 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(0 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (1 : usize)
      (0 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx4, bx0⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (9 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (1 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (2 : usize)
      (1 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(0 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (3 : usize)
      (1 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(1 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (4 : usize)
      (1 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx1, bx2, bx3⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (3 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (13 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (4 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (0 : usize)
      (1 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (1 : usize)
      (0 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (2 : usize)
      (1 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (3 : usize)
      (1 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (4 : usize)
      (1 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (0 : usize)
      (0 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(1 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (1 : usize)
      (1 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx4, bx0⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (9 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (0 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (2 : usize)
      (0 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(1 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (3 : usize)
      (0 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(0 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (4 : usize)
      (0 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx1, bx2, bx3⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (3 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (12 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (4 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (0 : usize)
      (0 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (1 : usize)
      (1 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (2 : usize)
      (0 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (3 : usize)
      (0 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (4 : usize)
      (0 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (0 : usize)
      (1 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(0 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (1 : usize)
      (1 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx1, bx2⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (18 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (5 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (2 : usize)
      (1 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(1 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (3 : usize)
      (1 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(0 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (4 : usize)
      (0 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx3, bx4, bx0⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (8 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (28 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (14 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (0 : usize)
      (1 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (1 : usize)
      (1 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (2 : usize)
      (1 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (3 : usize)
      (1 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (4 : usize)
      (0 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (0 : usize)
      (0 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(1 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (1 : usize)
      (0 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx1, bx2⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (18 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (5 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (2 : usize)
      (0 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(0 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (3 : usize)
      (0 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(1 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (4 : usize)
      (1 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx3, bx4, bx0⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (7 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (28 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (13 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (0 : usize)
      (0 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (1 : usize)
      (0 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (2 : usize)
      (0 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (3 : usize)
      (0 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (4 : usize)
      (1 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (0 : usize)
      (0 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(1 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (1 : usize)
      (0 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx3, bx4⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (21 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (1 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (2 : usize)
      (1 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(0 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (3 : usize)
      (0 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(1 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (4 : usize)
      (0 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx0, bx1, bx2⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (31 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (28 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (20 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (0 : usize)
      (0 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (1 : usize)
      (0 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (2 : usize)
      (1 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (3 : usize)
      (0 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (4 : usize)
      (0 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (0 : usize)
      (1 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(0 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (1 : usize)
      (1 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx3, bx4⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (20 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (1 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (2 : usize)
      (0 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(1 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (3 : usize)
      (1 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(0 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (4 : usize)
      (1 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx0, bx1, bx2⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (31 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (27 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (19 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (0 : usize)
      (1 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (1 : usize)
      (1 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (2 : usize)
      (0 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (3 : usize)
      (1 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (4 : usize)
      (1 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure s)

set_option maxRecDepth 1000 in

@[spec]
def keccakf1600_round3_pi_rho_chi_1 (BASE_ROUND : usize)
    (s : libcrux_iot_sha3.state.KeccakState) :
    RustM libcrux_iot_sha3.state.KeccakState := do
  let i : usize := (libcrux_iot_sha3.state.KeccakState.i s);
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (0 : usize)
      (0 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(0 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (1 : usize)
      (0 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx0, bx1⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (0 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (22 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (2 : usize)
      (0 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(1 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (3 : usize)
      (0 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(1 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (4 : usize)
      (0 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx2, bx3, bx4⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (22 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (11 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (7 : u32))));
  let ax0 : u32 := (0 : u32);
  let ax0 : u32 ←
    ((← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)))) ^^^? (← RC_INTERLEAVED_0[i]_?));
  let _ := rust_primitives.hax.Tuple0.mk;
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (0 : usize)
      (0 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (1 : usize)
      (0 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (2 : usize)
      (0 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (3 : usize)
      (0 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (4 : usize)
      (0 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (0 : usize)
      (1 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(1 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (1 : usize)
      (1 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx0, bx1⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (0 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (22 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (2 : usize)
      (1 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(0 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (3 : usize)
      (1 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(0 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (0 : usize)
      (4 : usize)
      (1 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx2, bx3, bx4⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (21 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (10 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (7 : u32))));
  let ax0 : u32 := (0 : u32);
  let ax0 : u32 ←
    ((← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)))) ^^^? (← RC_INTERLEAVED_1[i]_?));
  let s : libcrux_iot_sha3.state.KeccakState :=
    {s with i := (← (i +? (1 : usize)))};
  let _ := rust_primitives.hax.Tuple0.mk;
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (0 : usize)
      (1 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (1 : usize)
      (1 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (2 : usize)
      (1 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (3 : usize)
      (1 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (0 : usize)
      (4 : usize)
      (1 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (0 : usize)
      (0 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(1 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (1 : usize)
      (0 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx2, bx3⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (2 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (23 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (2 : usize)
      (0 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(1 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (3 : usize)
      (0 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(0 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (4 : usize)
      (0 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx4, bx0, bx1⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (31 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (14 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (10 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (0 : usize)
      (0 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (1 : usize)
      (0 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (2 : usize)
      (0 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (3 : usize)
      (0 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (4 : usize)
      (0 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (0 : usize)
      (1 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(0 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (1 : usize)
      (1 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx2, bx3⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (1 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (22 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (2 : usize)
      (1 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(0 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (3 : usize)
      (1 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(1 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (1 : usize)
      (4 : usize)
      (1 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx4, bx0, bx1⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (30 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (14 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (10 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (0 : usize)
      (1 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (1 : usize)
      (1 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (2 : usize)
      (1 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (3 : usize)
      (1 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (1 : usize)
      (4 : usize)
      (1 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure s)

set_option maxRecDepth 1500 in

@[spec]
def keccakf1600_round3_pi_rho_chi_2 (s : libcrux_iot_sha3.state.KeccakState) :
    RustM libcrux_iot_sha3.state.KeccakState := do
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (0 : usize)
      (0 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(0 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (1 : usize)
      (0 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx4, bx0⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (9 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (1 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (2 : usize)
      (0 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(0 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (3 : usize)
      (0 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(1 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (4 : usize)
      (0 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx1, bx2, bx3⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (3 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (13 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (4 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (0 : usize)
      (0 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (1 : usize)
      (0 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (2 : usize)
      (0 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (3 : usize)
      (0 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (4 : usize)
      (0 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (0 : usize)
      (1 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(1 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (1 : usize)
      (1 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx4, bx0⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (9 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (0 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (2 : usize)
      (1 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(1 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (3 : usize)
      (1 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(0 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (2 : usize)
      (4 : usize)
      (1 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx1, bx2, bx3⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (3 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (12 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (4 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (0 : usize)
      (1 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (1 : usize)
      (1 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (2 : usize)
      (1 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (3 : usize)
      (1 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (2 : usize)
      (4 : usize)
      (1 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (0 : usize)
      (0 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(0 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (1 : usize)
      (0 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx1, bx2⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (18 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (5 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (2 : usize)
      (0 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(1 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (3 : usize)
      (0 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(0 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (4 : usize)
      (0 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx3, bx4, bx0⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (8 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (28 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (14 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (0 : usize)
      (0 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (1 : usize)
      (0 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (2 : usize)
      (0 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (3 : usize)
      (0 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (4 : usize)
      (0 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (0 : usize)
      (1 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(1 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (1 : usize)
      (1 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx1, bx2⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (18 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (5 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (2 : usize)
      (1 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(0 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (3 : usize)
      (1 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(1 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (3 : usize)
      (4 : usize)
      (1 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx3, bx4, bx0⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (7 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (28 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (13 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (0 : usize)
      (1 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (1 : usize)
      (1 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (2 : usize)
      (1 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (3 : usize)
      (1 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (3 : usize)
      (4 : usize)
      (1 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (0 : usize)
      (0 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(1 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (1 : usize)
      (0 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx3, bx4⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (21 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (1 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (2 : usize)
      (0 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(0 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (3 : usize)
      (0 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(1 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (4 : usize)
      (0 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx0, bx1, bx2⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (31 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (28 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (20 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (0 : usize)
      (0 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (1 : usize)
      (0 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (2 : usize)
      (0 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (3 : usize)
      (0 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (4 : usize)
      (0 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  let a0 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (0 : usize)
      (1 : usize));
  let d0 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(0 : usize)]_?)[(0 : usize)]_?;
  let a1 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (1 : usize)
      (1 : usize));
  let d1 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(1 : usize)]_?)[(1 : usize)]_?;
  let ⟨bx3, bx4⟩ :=
    (rust_primitives.hax.Tuple2.mk
      (← (core_models.num.Impl_8.rotate_left (← (a0 ^^^? d0)) (20 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a1 ^^^? d1)) (1 : u32))));
  let a2 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (2 : usize)
      (1 : usize));
  let d2 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(2 : usize)]_?)[(1 : usize)]_?;
  let a3 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (3 : usize)
      (1 : usize));
  let d3 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(3 : usize)]_?)[(0 : usize)]_?;
  let a4 : u32 ←
    (libcrux_iot_sha3.state.Impl.get_with_zeta
      s
      (4 : usize)
      (4 : usize)
      (1 : usize));
  let d4 : u32 ←
    (← (libcrux_iot_sha3.state.KeccakState.d s)[(4 : usize)]_?)[(0 : usize)]_?;
  let ⟨bx0, bx1, bx2⟩ :=
    (rust_primitives.hax.Tuple3.mk
      (← (core_models.num.Impl_8.rotate_left (← (a2 ^^^? d2)) (31 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a3 ^^^? d3)) (27 : u32)))
      (← (core_models.num.Impl_8.rotate_left (← (a4 ^^^? d4)) (19 : u32))));
  let ax0 : u32 ← (bx0 ^^^? (← ((← (~? bx1)) &&&? bx2)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (0 : usize)
      (1 : usize)
      ax0);
  let ax1 : u32 ← (bx1 ^^^? (← ((← (~? bx2)) &&&? bx3)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (1 : usize)
      (1 : usize)
      ax1);
  let ax2 : u32 ← (bx2 ^^^? (← ((← (~? bx3)) &&&? bx4)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (2 : usize)
      (1 : usize)
      ax2);
  let ax3 : u32 ← (bx3 ^^^? (← ((← (~? bx4)) &&&? bx0)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (3 : usize)
      (1 : usize)
      ax3);
  let ax4 : u32 ← (bx4 ^^^? (← ((← (~? bx0)) &&&? bx1)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.set_with_zeta
      s
      (4 : usize)
      (4 : usize)
      (1 : usize)
      ax4);
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure s)

@[spec]
def keccakf1600_4rounds (BASE_ROUND : usize)
    (s : libcrux_iot_sha3.state.KeccakState) :
    RustM libcrux_iot_sha3.state.KeccakState := do
  let s : libcrux_iot_sha3.state.KeccakState ← (keccakf1600_round0_theta s);
  let s : libcrux_iot_sha3.state.KeccakState ←
    (keccakf1600_round0_pi_rho_chi_1 (BASE_ROUND) s);
  let s : libcrux_iot_sha3.state.KeccakState ←
    (keccakf1600_round0_pi_rho_chi_2 s);
  let s : libcrux_iot_sha3.state.KeccakState ← (keccakf1600_round1_theta s);
  let s : libcrux_iot_sha3.state.KeccakState ←
    (keccakf1600_round1_pi_rho_chi_1 (BASE_ROUND) s);
  let s : libcrux_iot_sha3.state.KeccakState ←
    (keccakf1600_round1_pi_rho_chi_2 s);
  let s : libcrux_iot_sha3.state.KeccakState ← (keccakf1600_round2_theta s);
  let s : libcrux_iot_sha3.state.KeccakState ←
    (keccakf1600_round2_pi_rho_chi_1 (BASE_ROUND) s);
  let s : libcrux_iot_sha3.state.KeccakState ←
    (keccakf1600_round2_pi_rho_chi_2 s);
  let s : libcrux_iot_sha3.state.KeccakState ← (keccakf1600_round3_theta s);
  let s : libcrux_iot_sha3.state.KeccakState ←
    (keccakf1600_round3_pi_rho_chi_1 (BASE_ROUND) s);
  let s : libcrux_iot_sha3.state.KeccakState ←
    (keccakf1600_round3_pi_rho_chi_2 s);
  (pure s)

@[spec]
def keccakf1600 (s : libcrux_iot_sha3.state.KeccakState) :
    RustM libcrux_iot_sha3.state.KeccakState := do
  let s : libcrux_iot_sha3.state.KeccakState ←
    (rust_primitives.hax.folds.fold_range
      (0 : i32)
      (6 : i32)
      (fun s _ => (do (pure true) : RustM Bool))
      s
      (fun s _ =>
        (do
        (keccakf1600_4rounds ((0 : usize)) s) :
        RustM libcrux_iot_sha3.state.KeccakState)));
  let s : libcrux_iot_sha3.state.KeccakState := {s with i := (0 : usize)};
  (pure s)

end libcrux_iot_sha3.keccak


namespace libcrux_iot_sha3.state

@[spec]
def Impl.get_lane (self : KeccakState) (i : usize) (j : usize) :
    RustM libcrux_iot_sha3.lane.Lane2U32 := do
  (KeccakState.st self)[(← ((← ((5 : usize) *? j)) +? i))]_?

@[spec]
def Impl.set_lane
    (self : KeccakState)
    (i : usize)
    (j : usize)
    (lane : libcrux_iot_sha3.lane.Lane2U32) :
    RustM KeccakState := do
  let self : KeccakState :=
    {self
    with st := (← (rust_primitives.hax.monomorphized_update_at.update_at_usize
      (KeccakState.st self)
      (← ((← ((5 : usize) *? j)) +? i))
      lane))};
  (pure self)

--  `out` has the exact size we want here. It must be less than or equal to `RATE`.
@[spec]
def Impl.store (RATE : usize) (self : KeccakState) (out : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let num_full_blocks : usize ←
    ((← (core_models.slice.Impl.len u8 out)) /? (8 : usize));
  let last_block_len : usize ←
    ((← (core_models.slice.Impl.len u8 out)) %? (8 : usize));
  let out : (RustSlice u8) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      num_full_blocks
      (fun out _ => (do (pure true) : RustM Bool))
      out
      (fun out i =>
        (do
        let lane : libcrux_iot_sha3.lane.Lane2U32 ←
          (libcrux_iot_sha3.lane.Impl.deinterleave
            (← (Impl.get_lane
              self
              (← (i /? (5 : usize)))
              (← (i %? (5 : usize))))));
        let out : (RustSlice u8) ←
          (rust_primitives.hax.monomorphized_update_at.update_at_range
            out
            (core_models.ops.range.Range.mk
              (start := (← (i *? (8 : usize))))
              (_end := (← ((← (i *? (8 : usize))) +? (4 : usize)))))
            (← (core_models.slice.Impl.copy_from_slice u8
              (← out[
                (core_models.ops.range.Range.mk
                  (start := (← (i *? (8 : usize))))
                  (_end := (← ((← (i *? (8 : usize))) +? (4 : usize)))))
                ]_?)
              (← (rust_primitives.unsize
                (← (core_models.num.Impl_8.to_le_bytes
                  (← lane[(0 : usize)]_?))))))));
        let out : (RustSlice u8) ←
          (rust_primitives.hax.monomorphized_update_at.update_at_range
            out
            (core_models.ops.range.Range.mk
              (start := (← ((← (i *? (8 : usize))) +? (4 : usize))))
              (_end := (← ((← (i *? (8 : usize))) +? (8 : usize)))))
            (← (core_models.slice.Impl.copy_from_slice u8
              (← out[
                (core_models.ops.range.Range.mk
                  (start := (← ((← (i *? (8 : usize))) +? (4 : usize))))
                  (_end := (← ((← (i *? (8 : usize))) +? (8 : usize)))))
                ]_?)
              (← (rust_primitives.unsize
                (← (core_models.num.Impl_8.to_le_bytes
                  (← lane[(1 : usize)]_?))))))));
        (pure out) :
        RustM (RustSlice u8))));
  let out : (RustSlice u8) ←
    if (← (last_block_len >? (4 : usize))) then do
      let lane : libcrux_iot_sha3.lane.Lane2U32 ←
        (libcrux_iot_sha3.lane.Impl.deinterleave
          (← (Impl.get_lane
            self
            (← (num_full_blocks /? (5 : usize)))
            (← (num_full_blocks %? (5 : usize))))));
      let last_half_block_len : usize ← (last_block_len -? (4 : usize));
      let out : (RustSlice u8) ←
        (rust_primitives.hax.monomorphized_update_at.update_at_range
          out
          (core_models.ops.range.Range.mk
            (start := (← (num_full_blocks *? (8 : usize))))
            (_end := (← ((← (num_full_blocks *? (8 : usize))) +? (4 : usize)))))
          (← (core_models.slice.Impl.copy_from_slice u8
            (← out[
              (core_models.ops.range.Range.mk
                (start := (← (num_full_blocks *? (8 : usize))))
                (_end := (← ((← (num_full_blocks *? (8 : usize)))
                  +? (4 : usize)))))
              ]_?)
            (← (rust_primitives.unsize
              (← (core_models.num.Impl_8.to_le_bytes
                (← lane[(0 : usize)]_?))))))));
      let out : (RustSlice u8) ←
        (rust_primitives.hax.monomorphized_update_at.update_at_range
          out
          (core_models.ops.range.Range.mk
            (start := (← ((← (num_full_blocks *? (8 : usize))) +? (4 : usize))))
            (_end := (← ((← (num_full_blocks *? (8 : usize)))
              +? last_block_len))))
          (← (core_models.slice.Impl.copy_from_slice u8
            (← out[
              (core_models.ops.range.Range.mk
                (start := (← ((← (num_full_blocks *? (8 : usize)))
                  +? (4 : usize))))
                (_end := (← ((← (num_full_blocks *? (8 : usize)))
                  +? last_block_len))))
              ]_?)
            (← (← (core_models.num.Impl_8.to_le_bytes (← lane[(1 : usize)]_?)))[
              (core_models.ops.range.Range.mk
                (start := (0 : usize))
                (_end := last_half_block_len))
              ]_?))));
      (pure out)
    else do
      if (← (last_block_len >? (0 : usize))) then do
        let lane : libcrux_iot_sha3.lane.Lane2U32 ←
          (libcrux_iot_sha3.lane.Impl.deinterleave
            (← (Impl.get_lane
              self
              (← (num_full_blocks /? (5 : usize)))
              (← (num_full_blocks %? (5 : usize))))));
        let out : (RustSlice u8) ←
          (rust_primitives.hax.monomorphized_update_at.update_at_range
            out
            (core_models.ops.range.Range.mk
              (start := (← (num_full_blocks *? (8 : usize))))
              (_end := (← ((← (num_full_blocks *? (8 : usize)))
                +? last_block_len))))
            (← (core_models.slice.Impl.copy_from_slice u8
              (← out[
                (core_models.ops.range.Range.mk
                  (start := (← (num_full_blocks *? (8 : usize))))
                  (_end := (← ((← (num_full_blocks *? (8 : usize)))
                    +? last_block_len))))
                ]_?)
              (← (← (core_models.num.Impl_8.to_le_bytes
                  (← lane[(0 : usize)]_?)))[
                (core_models.ops.range.Range.mk
                  (start := (0 : usize))
                  (_end := last_block_len))
                ]_?))));
        (pure out)
      else do
        (pure out);
  (pure out)

end libcrux_iot_sha3.state


namespace libcrux_iot_sha3.keccak

--  Squeeze `N` x `LEN` bytes.
@[spec]
def Impl.squeeze (RATE : usize)
    (self : (KeccakXofState (RATE)))
    (out : (RustSlice u8)) :
    RustM
    (rust_primitives.hax.Tuple2 (KeccakXofState (RATE)) (RustSlice u8))
    := do
  let self : (KeccakXofState (RATE)) ←
    if (KeccakXofState.sponge self) then do
      let self : (KeccakXofState (RATE)) :=
        {self with inner := (← (keccakf1600 (KeccakXofState.inner self)))};
      (pure self)
    else do
      (pure self);
  let out_len : usize ← (core_models.slice.Impl.len u8 out);
  let blocks : usize ← (out_len /? RATE);
  let last : usize ← (out_len -? (← (out_len %? RATE)));
  let mid : usize ←
    if (← (RATE >=? out_len)) then do (pure out_len) else do (pure RATE);
  let out : (RustSlice u8) ←
    (libcrux_iot_sha3.state.Impl.store (RATE) (KeccakXofState.inner self) out);
  let offset : usize := mid;
  let ⟨offset, out, self⟩ ←
    (rust_primitives.hax.folds.fold_range
      (1 : usize)
      blocks
      (fun ⟨offset, out, self⟩ _ => (do (pure true) : RustM Bool))
      (rust_primitives.hax.Tuple3.mk offset out self)
      (fun ⟨offset, out, self⟩ _ =>
        (do
        let self : (KeccakXofState (RATE)) :=
          {self with inner := (← (keccakf1600 (KeccakXofState.inner self)))};
        let out : (RustSlice u8) ←
          (rust_primitives.hax.monomorphized_update_at.update_at_range_from
            out
            (core_models.ops.range.RangeFrom.mk (start := offset))
            (← (libcrux_iot_sha3.state.Impl.store (RATE)
              (KeccakXofState.inner self)
              (← out[
                (core_models.ops.range.RangeFrom.mk (start := offset))
                ]_?))));
        let offset : usize ← (offset +? RATE);
        (pure (rust_primitives.hax.Tuple3.mk offset out self)) :
        RustM
        (rust_primitives.hax.Tuple3
          usize
          (RustSlice u8)
          (KeccakXofState (RATE))))));
  let ⟨out, self⟩ ←
    if (← (last <? out_len)) then do
      let self : (KeccakXofState (RATE)) :=
        {self with inner := (← (keccakf1600 (KeccakXofState.inner self)))};
      let out : (RustSlice u8) ←
        (rust_primitives.hax.monomorphized_update_at.update_at_range_from
          out
          (core_models.ops.range.RangeFrom.mk (start := offset))
          (← (libcrux_iot_sha3.state.Impl.store (RATE)
            (KeccakXofState.inner self)
            (← out[
              (core_models.ops.range.RangeFrom.mk (start := offset))
              ]_?))));
      (pure (rust_primitives.hax.Tuple2.mk out self))
    else do
      (pure (rust_primitives.hax.Tuple2.mk out self));
  let self : (KeccakXofState (RATE)) := {self with sponge := true};
  (pure (rust_primitives.hax.Tuple2.mk self out))

end libcrux_iot_sha3.keccak


namespace libcrux_iot_sha3.state

@[spec]
def load_block_2u32 (RATE : usize)
    (state : KeccakState)
    (blocks : (RustSlice u8))
    (start : usize) :
    RustM KeccakState := do
  let _ ←
    if true then do
      let _ ←
        (hax_lib.assert
          (← ((← (RATE <=? (← (core_models.slice.Impl.len u8 blocks))))
            &&? (← ((← (RATE %? (8 : usize))) ==? (0 : usize))))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let state_flat : (RustArray libcrux_iot_sha3.lane.Lane2U32 25) ←
    (rust_primitives.hax.repeat
      (← (libcrux_iot_sha3.lane.Impl.zero rust_primitives.hax.Tuple0.mk))
      (25 : usize));
  let state_flat : (RustArray libcrux_iot_sha3.lane.Lane2U32 25) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      (← (RATE /? (8 : usize)))
      (fun state_flat _ => (do (pure true) : RustM Bool))
      state_flat
      (fun state_flat i =>
        (do
        let offset : usize ← (start +? (← ((8 : usize) *? i)));
        let a : u32 ←
          (core_models.num.Impl_8.from_le_bytes
            (← (core_models.result.Impl.unwrap
              (RustArray u8 4)
              core_models.array.TryFromSliceError
              (← (core_models.convert.TryInto.try_into
                (RustSlice u8)
                (RustArray u8 4)
                (← blocks[
                  (core_models.ops.range.Range.mk
                    (start := offset)
                    (_end := (← (offset +? (4 : usize)))))
                  ]_?))))));
        let b : u32 ←
          (core_models.num.Impl_8.from_le_bytes
            (← (core_models.result.Impl.unwrap
              (RustArray u8 4)
              core_models.array.TryFromSliceError
              (← (core_models.convert.TryInto.try_into
                (RustSlice u8)
                (RustArray u8 4)
                (← blocks[
                  (core_models.ops.range.Range.mk
                    (start := (← (offset +? (4 : usize))))
                    (_end := (← (offset +? (8 : usize)))))
                  ]_?))))));
        let state_flat : (RustArray libcrux_iot_sha3.lane.Lane2U32 25) ←
          (rust_primitives.hax.monomorphized_update_at.update_at_usize
            state_flat
            i
            (← (libcrux_iot_sha3.lane.Impl.interleave
              (← (core_models.convert.From._from
                libcrux_iot_sha3.lane.Lane2U32
                (RustArray u32 2) (RustArray.ofVec #v[a, b]))))));
        (pure state_flat) :
        RustM (RustArray libcrux_iot_sha3.lane.Lane2U32 25))));
  let state : KeccakState ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      (← (RATE /? (8 : usize)))
      (fun state _ => (do (pure true) : RustM Bool))
      state
      (fun state i =>
        (do
        let got : libcrux_iot_sha3.lane.Lane2U32 ←
          (Impl.get_lane state (← (i /? (5 : usize))) (← (i %? (5 : usize))));
        let state : KeccakState ←
          (Impl.set_lane
            state
            (← (i /? (5 : usize)))
            (← (i %? (5 : usize)))
            (← (libcrux_iot_sha3.lane.Impl.from_ints
              (RustArray.ofVec #v[(← ((← got[(0 : usize)]_?)
                                      ^^^? (← (← state_flat[i]_?)[
                                        (0 : usize)
                                        ]_?))),
                                    (← ((← got[(1 : usize)]_?)
                                      ^^^? (← (← state_flat[i]_?)[
                                        (1 : usize)
                                        ]_?)))]))));
        (pure state) :
        RustM KeccakState)));
  (pure state)

@[spec]
def Impl.load_block (RATE : usize)
    (self : KeccakState)
    (blocks : (RustSlice u8))
    (start : usize) :
    RustM KeccakState := do
  let self : KeccakState ← (load_block_2u32 (RATE) self blocks start);
  (pure self)

end libcrux_iot_sha3.state


namespace libcrux_iot_sha3.keccak

@[spec]
def Impl.absorb_full (RATE : usize)
    (self : (KeccakXofState (RATE)))
    (inputs : (RustSlice u8)) :
    RustM (rust_primitives.hax.Tuple2 (KeccakXofState (RATE)) usize) := do
  let _ ←
    if true then do
      let _ ← (hax_lib.assert (← ((KeccakXofState.buf_len self) <? RATE)));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let ⟨tmp0, out⟩ ← (Impl.fill_buffer (RATE) self inputs);
  let self : (KeccakXofState (RATE)) := tmp0;
  let input_consumed : usize := out;
  let self : (KeccakXofState (RATE)) ←
    if (← (input_consumed >? (0 : usize))) then do
      let self : (KeccakXofState (RATE)) :=
        {self
        with inner := (← (libcrux_iot_sha3.state.Impl.load_block (RATE)
          (KeccakXofState.inner self)
          (← (rust_primitives.unsize (KeccakXofState.buf self)))
          (0 : usize)))};
      let self : (KeccakXofState (RATE)) :=
        {self with inner := (← (keccakf1600 (KeccakXofState.inner self)))};
      let self : (KeccakXofState (RATE)) := {self with buf_len := (0 : usize)};
      (pure self)
    else do
      (pure self);
  let input_to_consume : usize ←
    ((← (core_models.slice.Impl.len u8 inputs)) -? input_consumed);
  let num_blocks : usize ← (input_to_consume /? RATE);
  let remainder : usize ← (input_to_consume %? RATE);
  let self : (KeccakXofState (RATE)) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      num_blocks
      (fun self _ => (do (pure true) : RustM Bool))
      self
      (fun self i =>
        (do
        let self : (KeccakXofState (RATE)) :=
          {self
          with inner := (← (libcrux_iot_sha3.state.Impl.load_block (RATE)
            (KeccakXofState.inner self)
            inputs
            (← (input_consumed +? (← (i *? RATE))))))};
        let self : (KeccakXofState (RATE)) :=
          {self with inner := (← (keccakf1600 (KeccakXofState.inner self)))};
        (pure self) :
        RustM (KeccakXofState (RATE)))));
  let hax_temp_output : usize := remainder;
  (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))

--  Absorb
-- 
--  This function takes any number of bytes to absorb and buffers if it's not enough.
--  The function assumes that all input slices in `blocks` have the same length.
-- 
--  Only a multiple of `RATE` blocks are absorbed.
--  For the remaining bytes [`absorb_final`] needs to be called.
-- 
--  This works best with relatively small `inputs`.
@[spec]
def Impl.absorb (RATE : usize)
    (self : (KeccakXofState (RATE)))
    (inputs : (RustSlice u8)) :
    RustM (KeccakXofState (RATE)) := do
  let ⟨tmp0, out⟩ ← (Impl.absorb_full (RATE) self inputs);
  let self : (KeccakXofState (RATE)) := tmp0;
  let input_remainder_len : usize := out;
  let self : (KeccakXofState (RATE)) ←
    if (← (input_remainder_len >? (0 : usize))) then do
      let _ ←
        if true then do
          let _ ←
            (hax_lib.assert
              (← ((← ((KeccakXofState.buf_len self) ==? (0 : usize)))
                ||? (← ((← ((KeccakXofState.buf_len self)
                    +? input_remainder_len))
                  <=? RATE)))));
          (pure rust_primitives.hax.Tuple0.mk)
        else do
          (pure rust_primitives.hax.Tuple0.mk);
      let input_len : usize ← (core_models.slice.Impl.len u8 inputs);
      let self : (KeccakXofState (RATE)) :=
        {self
        with buf := (←
        (rust_primitives.hax.monomorphized_update_at.update_at_range
          (KeccakXofState.buf self)
          (core_models.ops.range.Range.mk
            (start := (KeccakXofState.buf_len self))
            (_end := (← ((KeccakXofState.buf_len self)
              +? input_remainder_len))))
          (← (core_models.slice.Impl.copy_from_slice u8
            (← (KeccakXofState.buf self)[
              (core_models.ops.range.Range.mk
                (start := (KeccakXofState.buf_len self))
                (_end := (← ((KeccakXofState.buf_len self)
                  +? input_remainder_len))))
              ]_?)
            (← inputs[
              (core_models.ops.range.RangeFrom.mk
                (start := (← (input_len -? input_remainder_len))))
              ]_?)))))};
      let self : (KeccakXofState (RATE)) :=
        {self
        with buf_len := (← ((KeccakXofState.buf_len self)
          +? input_remainder_len))};
      (pure self)
    else do
      (pure self);
  (pure self)

@[spec]
def absorb_block (RATE : usize)
    (s : libcrux_iot_sha3.state.KeccakState)
    (blocks : (RustSlice u8))
    (start : usize) :
    RustM libcrux_iot_sha3.state.KeccakState := do
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.load_block (RATE) s blocks start);
  let s : libcrux_iot_sha3.state.KeccakState ← (keccakf1600 s);
  (pure s)

end libcrux_iot_sha3.keccak


namespace libcrux_iot_sha3.state

@[spec]
def load_block_full_2u32 (RATE : usize)
    (state : KeccakState)
    (blocks : (RustArray u8 200))
    (start : usize) :
    RustM KeccakState := do
  let state : KeccakState ←
    (load_block_2u32 (RATE) state (← (rust_primitives.unsize blocks)) start);
  (pure state)

@[spec]
def Impl.load_block_full (RATE : usize)
    (self : KeccakState)
    (blocks : (RustArray u8 200))
    (start : usize) :
    RustM KeccakState := do
  let self : KeccakState ← (load_block_full_2u32 (RATE) self blocks start);
  (pure self)

end libcrux_iot_sha3.state


namespace libcrux_iot_sha3.keccak

--  Absorb a final block.
-- 
--  The `inputs` block may be empty. Everything in the `inputs` block beyond
--  `RATE` bytes is ignored.
@[spec]
def Impl.absorb_final (RATE : usize) (DELIMITER : u8)
    (self : (KeccakXofState (RATE)))
    (inputs : (RustSlice u8)) :
    RustM (KeccakXofState (RATE)) := do
  let ⟨tmp0, out⟩ ← (Impl.absorb_full (RATE) self inputs);
  let self : (KeccakXofState (RATE)) := tmp0;
  let input_remainder_len : usize := out;
  let input_len : usize ← (core_models.slice.Impl.len u8 inputs);
  let blocks : (RustArray u8 200) ←
    (libcrux_secrets.traits.Classify.classify
      (RustArray u8 200)
      (← (rust_primitives.hax.repeat (0 : u8) (200 : usize))));
  let blocks : (RustArray u8 200) ←
    if (← ((KeccakXofState.buf_len self) >? (0 : usize))) then do
      let blocks : (RustArray u8 200) ←
        (rust_primitives.hax.monomorphized_update_at.update_at_range
          blocks
          (core_models.ops.range.Range.mk
            (start := (0 : usize))
            (_end := (KeccakXofState.buf_len self)))
          (← (core_models.slice.Impl.copy_from_slice u8
            (← blocks[
              (core_models.ops.range.Range.mk
                (start := (0 : usize))
                (_end := (KeccakXofState.buf_len self)))
              ]_?)
            (← (KeccakXofState.buf self)[
              (core_models.ops.range.Range.mk
                (start := (0 : usize))
                (_end := (KeccakXofState.buf_len self)))
              ]_?))));
      (pure blocks)
    else do
      (pure blocks);
  let blocks : (RustArray u8 200) ←
    if (← (input_remainder_len >? (0 : usize))) then do
      let blocks : (RustArray u8 200) ←
        (rust_primitives.hax.monomorphized_update_at.update_at_range
          blocks
          (core_models.ops.range.Range.mk
            (start := (KeccakXofState.buf_len self))
            (_end := (← ((KeccakXofState.buf_len self)
              +? input_remainder_len))))
          (← (core_models.slice.Impl.copy_from_slice u8
            (← blocks[
              (core_models.ops.range.Range.mk
                (start := (KeccakXofState.buf_len self))
                (_end := (← ((KeccakXofState.buf_len self)
                  +? input_remainder_len))))
              ]_?)
            (← inputs[
              (core_models.ops.range.RangeFrom.mk
                (start := (← (input_len -? input_remainder_len))))
              ]_?))));
      (pure blocks)
    else do
      (pure blocks);
  let blocks : (RustArray u8 200) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      blocks
      (← ((KeccakXofState.buf_len self) +? input_remainder_len))
      (← (libcrux_secrets.traits.Classify.classify u8 DELIMITER)));
  let blocks : (RustArray u8 200) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      blocks
      (← (RATE -? (1 : usize)))
      (← ((← blocks[(← (RATE -? (1 : usize)))]_?) |||? (128 : u8))));
  let self : (KeccakXofState (RATE)) :=
    {self
    with inner := (← (libcrux_iot_sha3.state.Impl.load_block_full (RATE)
      (KeccakXofState.inner self)
      blocks
      (0 : usize)))};
  let self : (KeccakXofState (RATE)) :=
    {self with inner := (← (keccakf1600 (KeccakXofState.inner self)))};
  (pure self)

@[spec]
def absorb_final (RATE : usize) (DELIM : u8)
    (s : libcrux_iot_sha3.state.KeccakState)
    (last : (RustSlice u8))
    (start : usize)
    (len : usize) :
    RustM libcrux_iot_sha3.state.KeccakState := do
  let _ ←
    if true then do
      let _ ← (hax_lib.assert (← (len <? RATE)));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let blocks : (RustArray u8 200) ←
    (libcrux_secrets.traits.Classify.classify
      (RustArray u8 200)
      (← (rust_primitives.hax.repeat (0 : u8) (200 : usize))));
  let blocks : (RustArray u8 200) ←
    if (← (len >? (0 : usize))) then do
      let blocks : (RustArray u8 200) ←
        (rust_primitives.hax.monomorphized_update_at.update_at_range
          blocks
          (core_models.ops.range.Range.mk (start := (0 : usize)) (_end := len))
          (← (core_models.slice.Impl.copy_from_slice u8
            (← blocks[
              (core_models.ops.range.Range.mk
                (start := (0 : usize))
                (_end := len))
              ]_?)
            (← last[
              (core_models.ops.range.Range.mk
                (start := start)
                (_end := (← (start +? len))))
              ]_?))));
      (pure blocks)
    else do
      (pure blocks);
  let blocks : (RustArray u8 200) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      blocks
      len
      (← (libcrux_secrets.traits.Classify.classify u8 DELIM)));
  let blocks : (RustArray u8 200) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      blocks
      (← (RATE -? (1 : usize)))
      (← ((← blocks[(← (RATE -? (1 : usize)))]_?) |||? (128 : u8))));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.load_block_full (RATE) s blocks (0 : usize));
  let s : libcrux_iot_sha3.state.KeccakState ← (keccakf1600 s);
  (pure s)

end libcrux_iot_sha3.keccak


namespace libcrux_iot_sha3.state

@[spec]
def store_block_2u32 (RATE : usize) (s : KeccakState) (out : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let out : (RustSlice u8) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      (← (RATE /? (8 : usize)))
      (fun out _ => (do (pure true) : RustM Bool))
      out
      (fun out i =>
        (do
        let lane : libcrux_iot_sha3.lane.Lane2U32 ←
          (libcrux_iot_sha3.lane.Impl.deinterleave
            (← (Impl.get_lane
              s
              (← (i /? (5 : usize)))
              (← (i %? (5 : usize))))));
        let out : (RustSlice u8) ←
          (rust_primitives.hax.monomorphized_update_at.update_at_range
            out
            (core_models.ops.range.Range.mk
              (start := (← ((8 : usize) *? i)))
              (_end := (← ((← ((8 : usize) *? i)) +? (4 : usize)))))
            (← (core_models.slice.Impl.copy_from_slice u8
              (← out[
                (core_models.ops.range.Range.mk
                  (start := (← ((8 : usize) *? i)))
                  (_end := (← ((← ((8 : usize) *? i)) +? (4 : usize)))))
                ]_?)
              (← (rust_primitives.unsize
                (← (core_models.num.Impl_8.to_le_bytes
                  (← lane[(0 : usize)]_?))))))));
        let out : (RustSlice u8) ←
          (rust_primitives.hax.monomorphized_update_at.update_at_range
            out
            (core_models.ops.range.Range.mk
              (start := (← ((← ((8 : usize) *? i)) +? (4 : usize))))
              (_end := (← ((← ((8 : usize) *? i)) +? (8 : usize)))))
            (← (core_models.slice.Impl.copy_from_slice u8
              (← out[
                (core_models.ops.range.Range.mk
                  (start := (← ((← ((8 : usize) *? i)) +? (4 : usize))))
                  (_end := (← ((← ((8 : usize) *? i)) +? (8 : usize)))))
                ]_?)
              (← (rust_primitives.unsize
                (← (core_models.num.Impl_8.to_le_bytes
                  (← lane[(1 : usize)]_?))))))));
        (pure out) :
        RustM (RustSlice u8))));
  (pure out)

@[spec]
def Impl.store_block (RATE : usize)
    (self : KeccakState)
    (out : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let out : (RustSlice u8) ← (store_block_2u32 (RATE) self out);
  (pure out)

end libcrux_iot_sha3.state


namespace libcrux_iot_sha3.keccak

@[spec]
def squeeze_first_block (RATE : usize)
    (s : libcrux_iot_sha3.state.KeccakState)
    (out : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let out : (RustSlice u8) ←
    (libcrux_iot_sha3.state.Impl.store_block (RATE) s out);
  (pure out)

@[spec]
def squeeze_next_block (RATE : usize)
    (s : libcrux_iot_sha3.state.KeccakState)
    (out : (RustSlice u8)) :
    RustM
    (rust_primitives.hax.Tuple2
      libcrux_iot_sha3.state.KeccakState
      (RustSlice u8))
    := do
  let s : libcrux_iot_sha3.state.KeccakState ← (keccakf1600 s);
  let out : (RustSlice u8) ←
    (libcrux_iot_sha3.state.Impl.store_block (RATE) s out);
  (pure (rust_primitives.hax.Tuple2.mk s out))

@[spec]
def squeeze_first_three_blocks (RATE : usize)
    (s : libcrux_iot_sha3.state.KeccakState)
    (out : (RustSlice u8)) :
    RustM
    (rust_primitives.hax.Tuple2
      libcrux_iot_sha3.state.KeccakState
      (RustSlice u8))
    := do
  let out : (RustSlice u8) ← (squeeze_first_block (RATE) s out);
  let ⟨tmp0, tmp1⟩ ←
    (squeeze_next_block (RATE)
      s
      (← out[(core_models.ops.range.RangeFrom.mk (start := RATE))]_?));
  let s : libcrux_iot_sha3.state.KeccakState := tmp0;
  let out : (RustSlice u8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_range_from
      out
      (core_models.ops.range.RangeFrom.mk (start := RATE))
      tmp1);
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ←
    (squeeze_next_block (RATE)
      s
      (← out[
        (core_models.ops.range.RangeFrom.mk
          (start := (← ((2 : usize) *? RATE))))
        ]_?));
  let s : libcrux_iot_sha3.state.KeccakState := tmp0;
  let out : (RustSlice u8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_range_from
      out
      (core_models.ops.range.RangeFrom.mk (start := (← ((2 : usize) *? RATE))))
      tmp1);
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure (rust_primitives.hax.Tuple2.mk s out))

@[spec]
def squeeze_first_five_blocks (RATE : usize)
    (s : libcrux_iot_sha3.state.KeccakState)
    (out : (RustSlice u8)) :
    RustM
    (rust_primitives.hax.Tuple2
      libcrux_iot_sha3.state.KeccakState
      (RustSlice u8))
    := do
  let out : (RustSlice u8) ← (squeeze_first_block (RATE) s out);
  let ⟨tmp0, tmp1⟩ ←
    (squeeze_next_block (RATE)
      s
      (← out[(core_models.ops.range.RangeFrom.mk (start := RATE))]_?));
  let s : libcrux_iot_sha3.state.KeccakState := tmp0;
  let out : (RustSlice u8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_range_from
      out
      (core_models.ops.range.RangeFrom.mk (start := RATE))
      tmp1);
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ←
    (squeeze_next_block (RATE)
      s
      (← out[
        (core_models.ops.range.RangeFrom.mk
          (start := (← ((2 : usize) *? RATE))))
        ]_?));
  let s : libcrux_iot_sha3.state.KeccakState := tmp0;
  let out : (RustSlice u8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_range_from
      out
      (core_models.ops.range.RangeFrom.mk (start := (← ((2 : usize) *? RATE))))
      tmp1);
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ←
    (squeeze_next_block (RATE)
      s
      (← out[
        (core_models.ops.range.RangeFrom.mk
          (start := (← ((3 : usize) *? RATE))))
        ]_?));
  let s : libcrux_iot_sha3.state.KeccakState := tmp0;
  let out : (RustSlice u8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_range_from
      out
      (core_models.ops.range.RangeFrom.mk (start := (← ((3 : usize) *? RATE))))
      tmp1);
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ←
    (squeeze_next_block (RATE)
      s
      (← out[
        (core_models.ops.range.RangeFrom.mk
          (start := (← ((4 : usize) *? RATE))))
        ]_?));
  let s : libcrux_iot_sha3.state.KeccakState := tmp0;
  let out : (RustSlice u8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_range_from
      out
      (core_models.ops.range.RangeFrom.mk (start := (← ((4 : usize) *? RATE))))
      tmp1);
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure (rust_primitives.hax.Tuple2.mk s out))

end libcrux_iot_sha3.keccak


namespace libcrux_iot_sha3.state

@[spec]
def store_block_full_2u32 (RATE : usize)
    (s : KeccakState)
    (out : (RustArray u8 200)) :
    RustM (RustArray u8 200) := do
  let out : (RustArray u8 200) ← (store_block_2u32 (RATE) s out);
  (pure out)

@[spec]
def Impl.store_block_full (RATE : usize)
    (self : KeccakState)
    (out : (RustArray u8 200)) :
    RustM (RustArray u8 200) := do
  let out : (RustArray u8 200) ← (store_block_full_2u32 (RATE) self out);
  (pure out)

end libcrux_iot_sha3.state


namespace libcrux_iot_sha3.keccak

@[spec]
def squeeze_last (RATE : usize)
    (s : libcrux_iot_sha3.state.KeccakState)
    (out : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let s : libcrux_iot_sha3.state.KeccakState ← (keccakf1600 s);
  let b : (RustArray u8 200) ←
    (libcrux_secrets.traits.Classify.classify
      (RustArray u8 200)
      (← (rust_primitives.hax.repeat (0 : u8) (200 : usize))));
  let b : (RustArray u8 200) ←
    (libcrux_iot_sha3.state.Impl.store_block_full (RATE) s b);
  let out : (RustSlice u8) ←
    (core_models.slice.Impl.copy_from_slice u8
      out
      (← b[
        (core_models.ops.range.Range.mk
          (start := (0 : usize))
          (_end := (← (core_models.slice.Impl.len u8 out))))
        ]_?));
  (pure out)

@[spec]
def squeeze_first_and_last (RATE : usize)
    (s : libcrux_iot_sha3.state.KeccakState)
    (out : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let b : (RustArray u8 200) ←
    (libcrux_secrets.traits.Classify.classify
      (RustArray u8 200)
      (← (rust_primitives.hax.repeat (0 : u8) (200 : usize))));
  let b : (RustArray u8 200) ←
    (libcrux_iot_sha3.state.Impl.store_block_full (RATE) s b);
  let out : (RustSlice u8) ←
    (core_models.slice.Impl.copy_from_slice u8
      out
      (← b[
        (core_models.ops.range.Range.mk
          (start := (0 : usize))
          (_end := (← (core_models.slice.Impl.len u8 out))))
        ]_?));
  (pure out)

@[spec]
def keccak (RATE : usize) (DELIM : u8)
    (data : (RustSlice u8))
    (out : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let n : usize ← ((← (core_models.slice.Impl.len u8 data)) /? RATE);
  let rem : usize ← ((← (core_models.slice.Impl.len u8 data)) %? RATE);
  let outlen : usize ← (core_models.slice.Impl.len u8 out);
  let blocks : usize ← (outlen /? RATE);
  let last : usize ← (outlen -? (← (outlen %? RATE)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (libcrux_iot_sha3.state.Impl.new rust_primitives.hax.Tuple0.mk);
  let s : libcrux_iot_sha3.state.KeccakState ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      n
      (fun s _ => (do (pure true) : RustM Bool))
      s
      (fun s i =>
        (do
        (absorb_block (RATE) s data (← (i *? RATE))) :
        RustM libcrux_iot_sha3.state.KeccakState)));
  let s : libcrux_iot_sha3.state.KeccakState ←
    (absorb_final (RATE) (DELIM)
      s
      data
      (← ((← (core_models.slice.Impl.len u8 data)) -? rem))
      rem);
  let ⟨out, s⟩ ←
    if (← (blocks ==? (0 : usize))) then do
      (pure (rust_primitives.hax.Tuple2.mk
        (← (squeeze_first_and_last (RATE) s out))
        s))
    else do
      let out : (RustSlice u8) ← (squeeze_first_block (RATE) s out);
      let offset : usize := RATE;
      let ⟨offset, out, s⟩ ←
        (rust_primitives.hax.folds.fold_range
          (1 : usize)
          blocks
          (fun ⟨offset, out, s⟩ _ => (do (pure true) : RustM Bool))
          (rust_primitives.hax.Tuple3.mk offset out s)
          (fun ⟨offset, out, s⟩ _i =>
            (do
            let ⟨tmp0, tmp1⟩ ←
              (squeeze_next_block (RATE)
                s
                (← out[
                  (core_models.ops.range.RangeFrom.mk (start := offset))
                  ]_?));
            let s : libcrux_iot_sha3.state.KeccakState := tmp0;
            let out : (RustSlice u8) ←
              (rust_primitives.hax.monomorphized_update_at.update_at_range_from
                out
                (core_models.ops.range.RangeFrom.mk (start := offset))
                tmp1);
            let _ := rust_primitives.hax.Tuple0.mk;
            let offset : usize ← (offset +? RATE);
            (pure (rust_primitives.hax.Tuple3.mk offset out s)) :
            RustM
            (rust_primitives.hax.Tuple3
              usize
              (RustSlice u8)
              libcrux_iot_sha3.state.KeccakState))));
      if (← (last <? outlen)) then do
        (pure (rust_primitives.hax.Tuple2.mk
          (← (rust_primitives.hax.monomorphized_update_at.update_at_range_from
            out
            (core_models.ops.range.RangeFrom.mk (start := offset))
            (← (squeeze_last (RATE)
              s
              (← out[
                (core_models.ops.range.RangeFrom.mk (start := offset))
                ]_?)))))
          s))
      else do
        (pure (rust_primitives.hax.Tuple2.mk out s));
  (pure out)

end libcrux_iot_sha3.keccak


namespace libcrux_iot_sha3

--  Size in bytes of a SHA3 244 digest.
def SHA3_224_DIGEST_SIZE : usize :=
  RustM.of_isOk (do (pure (28 : usize))) (by rfl)

--  Size in bytes of a SHA3 256 digest.
def SHA3_256_DIGEST_SIZE : usize :=
  RustM.of_isOk (do (pure (32 : usize))) (by rfl)

--  Size in bytes of a SHA3 2384 digest.
def SHA3_384_DIGEST_SIZE : usize :=
  RustM.of_isOk (do (pure (48 : usize))) (by rfl)

--  Size in bytes of a SHA3 512 digest.
def SHA3_512_DIGEST_SIZE : usize :=
  RustM.of_isOk (do (pure (64 : usize))) (by rfl)

--  The Digest Algorithm.
inductive Algorithm : Type
| --  SHA3 224
    Sha224 : Algorithm
| --  SHA3 256
    Sha256 : Algorithm
| --  SHA3 384
    Sha384 : Algorithm
| --  SHA3 512
    Sha512 : Algorithm

def Algorithm.Sha224.AnonConst : u32 :=
  RustM.of_isOk (do (pure (1 : u32))) (by rfl)

def Algorithm.Sha256.AnonConst : u32 :=
  RustM.of_isOk (do (pure (2 : u32))) (by rfl)

def Algorithm.Sha384.AnonConst : u32 :=
  RustM.of_isOk (do (pure (3 : u32))) (by rfl)

def Algorithm.Sha512.AnonConst : u32 :=
  RustM.of_isOk (do (pure (4 : u32))) (by rfl)

@[spec]
def Algorithm_cast_to_repr (x : Algorithm) : RustM u32 := do
  match x with
    | (Algorithm.Sha224 ) => do (pure Algorithm.Sha224.AnonConst)
    | (Algorithm.Sha256 ) => do (pure Algorithm.Sha256.AnonConst)
    | (Algorithm.Sha384 ) => do (pure Algorithm.Sha384.AnonConst)
    | (Algorithm.Sha512 ) => do (pure Algorithm.Sha512.AnonConst)

@[instance] opaque Impl_3.AssociatedTypes :
  core_models.clone.Clone.AssociatedTypes Algorithm :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3 :
  core_models.clone.Clone Algorithm :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2.AssociatedTypes :
  core_models.marker.Copy.AssociatedTypes Algorithm :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2 :
  core_models.marker.Copy Algorithm :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4.AssociatedTypes :
  core_models.fmt.Debug.AssociatedTypes Algorithm :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4 :
  core_models.fmt.Debug Algorithm :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5.AssociatedTypes :
  core_models.marker.StructuralPartialEq.AssociatedTypes Algorithm :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5 :
  core_models.marker.StructuralPartialEq Algorithm :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_6.AssociatedTypes :
  core_models.cmp.PartialEq.AssociatedTypes Algorithm Algorithm :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_6 :
  core_models.cmp.PartialEq Algorithm Algorithm :=
  by constructor <;> exact Inhabited.default

@[reducible] instance Impl.AssociatedTypes :
  core_models.convert.From.AssociatedTypes Algorithm u32
  where

instance Impl : core_models.convert.From Algorithm u32 where
  _from := fun (v : u32) => do
    match v with
      | 1 => do (pure Algorithm.Sha224)
      | 2 => do (pure Algorithm.Sha256)
      | 3 => do (pure Algorithm.Sha384)
      | 4 => do (pure Algorithm.Sha512)
      | _ => do
        (rust_primitives.hax.never_to_any
          (← (core_models.panicking.panic "explicit panic")))

@[reducible] instance Impl_1.AssociatedTypes :
  core_models.convert.From.AssociatedTypes u32 Algorithm
  where

instance Impl_1 : core_models.convert.From u32 Algorithm where
  _from := fun (v : Algorithm) => do
    match v with
      | (Algorithm.Sha224 ) => do (pure (1 : u32))
      | (Algorithm.Sha256 ) => do (pure (2 : u32))
      | (Algorithm.Sha384 ) => do (pure (3 : u32))
      | (Algorithm.Sha512 ) => do (pure (4 : u32))

--  Returns the output size of a digest.
@[spec]
def digest_size (mode : Algorithm) : RustM usize := do
  match mode with
    | (Algorithm.Sha224 ) => do (pure SHA3_224_DIGEST_SIZE)
    | (Algorithm.Sha256 ) => do (pure SHA3_256_DIGEST_SIZE)
    | (Algorithm.Sha384 ) => do (pure SHA3_384_DIGEST_SIZE)
    | (Algorithm.Sha512 ) => do (pure SHA3_512_DIGEST_SIZE)

end libcrux_iot_sha3


namespace libcrux_iot_sha3.portable

--  The Keccak state for the incremental API.
structure KeccakState where
  state : libcrux_iot_sha3.state.KeccakState

@[instance] opaque Impl_2.AssociatedTypes :
  core_models.fmt.Debug.AssociatedTypes KeccakState :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2 :
  core_models.fmt.Debug KeccakState :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl.AssociatedTypes :
  core_models.clone.Clone.AssociatedTypes KeccakState :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl :
  core_models.clone.Clone KeccakState :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1.AssociatedTypes :
  core_models.marker.Copy.AssociatedTypes KeccakState :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1 :
  core_models.marker.Copy KeccakState :=
  by constructor <;> exact Inhabited.default

@[spec]
def keccakx1 (RATE : usize) (DELIM : u8)
    (data : (RustSlice u8))
    (out : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let out : (RustSlice u8) ←
    (libcrux_iot_sha3.keccak.keccak (RATE) (DELIM) data out);
  (pure out)

end libcrux_iot_sha3.portable


namespace libcrux_iot_sha3

--  SHA3 224
-- 
--  Preconditions:
--  - `digest.len() == 28`
@[spec]
def sha224_ema (digest : (RustSlice u8)) (payload : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let _ ←
    if true then do
      let _ ←
        (hax_lib.assert
          (← ((← (core_models.slice.Impl.len u8 payload))
            <=? (← (rust_primitives.hax.cast_op
              core_models.num.Impl_8.MAX :
              RustM usize)))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let _ ←
    if true then do
      let _ ←
        (hax_lib.assert
          (← ((← (core_models.slice.Impl.len u8 digest)) ==? (28 : usize))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let digest : (RustSlice u8) ←
    (libcrux_iot_sha3.portable.keccakx1 ((144 : usize)) ((6 : u8))
      payload
      digest);
  (pure digest)

--  SHA3 224
@[spec]
def sha224 (data : (RustSlice u8)) : RustM (RustArray u8 28) := do
  let out : (RustArray u8 28) ←
    (libcrux_secrets.traits.Classify.classify
      (RustArray u8 28) (← (rust_primitives.hax.repeat (0 : u8) (28 : usize))));
  let out : (RustArray u8 28) ← (sha224_ema out data);
  (pure out)

--  SHA3 256
@[spec]
def sha256_ema (digest : (RustSlice u8)) (payload : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let _ ←
    if true then do
      let _ ←
        (hax_lib.assert
          (← ((← (core_models.slice.Impl.len u8 payload))
            <=? (← (rust_primitives.hax.cast_op
              core_models.num.Impl_8.MAX :
              RustM usize)))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let _ ←
    if true then do
      let _ ←
        (hax_lib.assert
          (← ((← (core_models.slice.Impl.len u8 digest)) ==? (32 : usize))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let digest : (RustSlice u8) ←
    (libcrux_iot_sha3.portable.keccakx1 ((136 : usize)) ((6 : u8))
      payload
      digest);
  (pure digest)

--  SHA3 256
@[spec]
def sha256 (data : (RustSlice u8)) : RustM (RustArray u8 32) := do
  let out : (RustArray u8 32) ←
    (libcrux_secrets.traits.Classify.classify
      (RustArray u8 32) (← (rust_primitives.hax.repeat (0 : u8) (32 : usize))));
  let out : (RustArray u8 32) ← (sha256_ema out data);
  (pure out)

--  SHA3 384
@[spec]
def sha384_ema (digest : (RustSlice u8)) (payload : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let _ ←
    if true then do
      let _ ←
        (hax_lib.assert
          (← ((← (core_models.slice.Impl.len u8 payload))
            <=? (← (rust_primitives.hax.cast_op
              core_models.num.Impl_8.MAX :
              RustM usize)))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let _ ←
    if true then do
      let _ ←
        (hax_lib.assert
          (← ((← (core_models.slice.Impl.len u8 digest)) ==? (48 : usize))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let digest : (RustSlice u8) ←
    (libcrux_iot_sha3.portable.keccakx1 ((104 : usize)) ((6 : u8))
      payload
      digest);
  (pure digest)

--  SHA3 384
@[spec]
def sha384 (data : (RustSlice u8)) : RustM (RustArray u8 48) := do
  let out : (RustArray u8 48) ←
    (libcrux_secrets.traits.Classify.classify
      (RustArray u8 48) (← (rust_primitives.hax.repeat (0 : u8) (48 : usize))));
  let out : (RustArray u8 48) ← (sha384_ema out data);
  (pure out)

--  SHA3 512
@[spec]
def sha512_ema (digest : (RustSlice u8)) (payload : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let _ ←
    if true then do
      let _ ←
        (hax_lib.assert
          (← ((← (core_models.slice.Impl.len u8 payload))
            <=? (← (rust_primitives.hax.cast_op
              core_models.num.Impl_8.MAX :
              RustM usize)))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let _ ←
    if true then do
      let _ ←
        (hax_lib.assert
          (← ((← (core_models.slice.Impl.len u8 digest)) ==? (64 : usize))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let digest : (RustSlice u8) ←
    (libcrux_iot_sha3.portable.keccakx1 ((72 : usize)) ((6 : u8))
      payload
      digest);
  (pure digest)

--  SHA3 512
@[spec]
def sha512 (data : (RustSlice u8)) : RustM (RustArray u8 64) := do
  let out : (RustArray u8 64) ←
    (libcrux_secrets.traits.Classify.classify
      (RustArray u8 64) (← (rust_primitives.hax.repeat (0 : u8) (64 : usize))));
  let out : (RustArray u8 64) ← (sha512_ema out data);
  (pure out)

--  SHAKE 128
-- 
--  Note that the output length `BYTES` must fit into 32 bit. If it is longer,
--  the output will only return `u32::MAX` bytes.
@[spec]
def shake128 (BYTES : usize) (data : (RustSlice u8)) :
    RustM (RustArray u8 BYTES) := do
  let out : (RustArray u8 BYTES) ←
    (libcrux_secrets.traits.Classify.classify
      (RustArray u8 BYTES) (← (rust_primitives.hax.repeat (0 : u8) BYTES)));
  let out : (RustArray u8 BYTES) ←
    (libcrux_iot_sha3.portable.keccakx1 ((168 : usize)) ((31 : u8)) data out);
  (pure out)

--  SHAKE 128
-- 
--  Writes `out.len()` bytes.
@[spec]
def shake128_ema (out : (RustSlice u8)) (data : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let out : (RustSlice u8) ←
    (libcrux_iot_sha3.portable.keccakx1 ((168 : usize)) ((31 : u8)) data out);
  (pure out)

--  SHAKE 256
-- 
--  Note that the output length `BYTES` must fit into 32 bit. If it is longer,
--  the output will only return `u32::MAX` bytes.
@[spec]
def shake256 (BYTES : usize) (data : (RustSlice u8)) :
    RustM (RustArray u8 BYTES) := do
  let out : (RustArray u8 BYTES) ←
    (libcrux_secrets.traits.Classify.classify
      (RustArray u8 BYTES) (← (rust_primitives.hax.repeat (0 : u8) BYTES)));
  let out : (RustArray u8 BYTES) ←
    (libcrux_iot_sha3.portable.keccakx1 ((136 : usize)) ((31 : u8)) data out);
  (pure out)

--  SHAKE 256
-- 
--  Writes `out.len()` bytes.
@[spec]
def shake256_ema (out : (RustSlice u8)) (data : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let out : (RustSlice u8) ←
    (libcrux_iot_sha3.portable.keccakx1 ((136 : usize)) ((31 : u8)) data out);
  (pure out)

end libcrux_iot_sha3


namespace libcrux_iot_sha3.portable

--  A portable SHA3 224 implementation.
@[spec]
def sha224 (digest : (RustSlice u8)) (data : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let digest : (RustSlice u8) ←
    (keccakx1 ((144 : usize)) ((6 : u8)) data digest);
  (pure digest)

--  A portable SHA3 256 implementation.
@[spec]
def sha256 (digest : (RustSlice u8)) (data : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let digest : (RustSlice u8) ←
    (keccakx1 ((136 : usize)) ((6 : u8)) data digest);
  (pure digest)

--  A portable SHA3 384 implementation.
@[spec]
def sha384 (digest : (RustSlice u8)) (data : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let digest : (RustSlice u8) ←
    (keccakx1 ((104 : usize)) ((6 : u8)) data digest);
  (pure digest)

--  A portable SHA3 512 implementation.
@[spec]
def sha512 (digest : (RustSlice u8)) (data : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let digest : (RustSlice u8) ←
    (keccakx1 ((72 : usize)) ((6 : u8)) data digest);
  (pure digest)

end libcrux_iot_sha3.portable


namespace libcrux_iot_sha3

--  SHA3
@[spec]
def hash (LEN : usize) (algorithm : Algorithm) (payload : (RustSlice u8)) :
    RustM (RustArray u8 LEN) := do
  let _ ←
    if true then do
      let _ ←
        (hax_lib.assert
          (← ((← (core_models.slice.Impl.len u8 payload))
            <=? (← (rust_primitives.hax.cast_op
              core_models.num.Impl_8.MAX :
              RustM usize)))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let out : (RustArray u8 LEN) ←
    (libcrux_secrets.traits.Classify.classify
      (RustArray u8 LEN) (← (rust_primitives.hax.repeat (0 : u8) LEN)));
  let out : (RustArray u8 LEN) ←
    match algorithm with
      | (Algorithm.Sha224 ) => do (libcrux_iot_sha3.portable.sha224 out payload)
      | (Algorithm.Sha256 ) => do (libcrux_iot_sha3.portable.sha256 out payload)
      | (Algorithm.Sha384 ) => do (libcrux_iot_sha3.portable.sha384 out payload)
      | (Algorithm.Sha512 ) => do
        (libcrux_iot_sha3.portable.sha512 out payload);
  (pure out)

end libcrux_iot_sha3


namespace libcrux_iot_sha3.portable

--  A portable SHAKE128 implementation.
@[spec]
def shake128 (digest : (RustSlice u8)) (data : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let digest : (RustSlice u8) ←
    (keccakx1 ((168 : usize)) ((31 : u8)) data digest);
  (pure digest)

--  A portable SHAKE256 implementation.
@[spec]
def shake256 (digest : (RustSlice u8)) (data : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let digest : (RustSlice u8) ←
    (keccakx1 ((136 : usize)) ((31 : u8)) data digest);
  (pure digest)

end libcrux_iot_sha3.portable


namespace libcrux_iot_sha3.portable.incremental.private

class Sealed.AssociatedTypes (Self : Type) where

class Sealed (Self : Type)
  [associatedTypes : outParam (Sealed.AssociatedTypes (Self : Type))]
  where

end libcrux_iot_sha3.portable.incremental.private


namespace libcrux_iot_sha3.portable.incremental

--  SHAKE128 Xof state
structure Shake128Xof where
  state : (libcrux_iot_sha3.keccak.KeccakXofState ((168 : usize)))

end libcrux_iot_sha3.portable.incremental


namespace libcrux_iot_sha3.portable.incremental.private

@[reducible] instance Impl.AssociatedTypes :
  Sealed.AssociatedTypes libcrux_iot_sha3.portable.incremental.Shake128Xof
  where

instance Impl : Sealed libcrux_iot_sha3.portable.incremental.Shake128Xof where

end libcrux_iot_sha3.portable.incremental.private


namespace libcrux_iot_sha3.portable.incremental

--  SHAKE256 Xof state
structure Shake256Xof where
  state : (libcrux_iot_sha3.keccak.KeccakXofState ((136 : usize)))

end libcrux_iot_sha3.portable.incremental


namespace libcrux_iot_sha3.portable.incremental.private

@[reducible] instance Impl_1.AssociatedTypes :
  Sealed.AssociatedTypes libcrux_iot_sha3.portable.incremental.Shake256Xof
  where

instance Impl_1 : Sealed libcrux_iot_sha3.portable.incremental.Shake256Xof where

end libcrux_iot_sha3.portable.incremental.private


namespace libcrux_iot_sha3.portable.incremental

--  An XOF
class Xof.AssociatedTypes (Self : Type) (RATE : usize) where
  [trait_constr_Xof_i0 :
  libcrux_iot_sha3.portable.incremental.private.Sealed.AssociatedTypes
  Self]

attribute [instance_reducible, instance] Xof.AssociatedTypes.trait_constr_Xof_i0

class Xof (Self : Type) (RATE : usize)
  [associatedTypes : outParam (Xof.AssociatedTypes (Self : Type) (RATE :
      usize))]
  where
  [trait_constr_Xof_i0 :
  libcrux_iot_sha3.portable.incremental.private.Sealed
  Self]
  new (Self) (RATE) : (rust_primitives.hax.Tuple0 -> RustM Self)
  absorb (Self) (RATE) : (Self -> (RustSlice u8) -> RustM Self)
  absorb_final (Self) (RATE) : (Self -> (RustSlice u8) -> RustM Self)
  squeeze (Self) (RATE) :
    (Self ->
    (RustSlice u8) ->
    RustM (rust_primitives.hax.Tuple2 Self (RustSlice u8)))

attribute [instance_reducible, instance] Xof.trait_constr_Xof_i0

@[reducible] instance Impl.AssociatedTypes :
  Xof.AssociatedTypes Shake128Xof ((168 : usize))
  where

instance Impl : Xof Shake128Xof ((168 : usize)) where
  new := fun (_ : rust_primitives.hax.Tuple0) => do
    (pure (Shake128Xof.mk
      (state := (← (libcrux_iot_sha3.keccak.Impl.new ((168 : usize))
        rust_primitives.hax.Tuple0.mk)))))
  absorb := fun (self : Shake128Xof) (input : (RustSlice u8)) => do
    let self : Shake128Xof :=
      {self
      with state := (← (libcrux_iot_sha3.keccak.Impl.absorb ((168 : usize))
        (Shake128Xof.state self)
        input))};
    (pure self)
  absorb_final := fun (self : Shake128Xof) (input : (RustSlice u8)) => do
    let self : Shake128Xof :=
      {self
      with state := (← (libcrux_iot_sha3.keccak.Impl.absorb_final
        ((168 : usize))
        ((31 : u8)) (Shake128Xof.state self) input))};
    (pure self)
  squeeze := fun (self : Shake128Xof) (out : (RustSlice u8)) => do
    let ⟨tmp0, tmp1⟩ ←
      (libcrux_iot_sha3.keccak.Impl.squeeze ((168 : usize))
        (Shake128Xof.state self)
        out);
    let self : Shake128Xof := {self with state := tmp0};
    let out : (RustSlice u8) := tmp1;
    let _ := rust_primitives.hax.Tuple0.mk;
    (pure (rust_primitives.hax.Tuple2.mk self out))

--  Shake256 XOF in absorb state
@[reducible] instance Impl_1.AssociatedTypes :
  Xof.AssociatedTypes Shake256Xof ((136 : usize))
  where

instance Impl_1 : Xof Shake256Xof ((136 : usize)) where
  new := fun (_ : rust_primitives.hax.Tuple0) => do
    (pure (Shake256Xof.mk
      (state := (← (libcrux_iot_sha3.keccak.Impl.new ((136 : usize))
        rust_primitives.hax.Tuple0.mk)))))
  absorb := fun (self : Shake256Xof) (input : (RustSlice u8)) => do
    let self : Shake256Xof :=
      {self
      with state := (← (libcrux_iot_sha3.keccak.Impl.absorb ((136 : usize))
        (Shake256Xof.state self)
        input))};
    (pure self)
  absorb_final := fun (self : Shake256Xof) (input : (RustSlice u8)) => do
    let self : Shake256Xof :=
      {self
      with state := (← (libcrux_iot_sha3.keccak.Impl.absorb_final
        ((136 : usize))
        ((31 : u8)) (Shake256Xof.state self) input))};
    (pure self)
  squeeze := fun (self : Shake256Xof) (out : (RustSlice u8)) => do
    let ⟨tmp0, tmp1⟩ ←
      (libcrux_iot_sha3.keccak.Impl.squeeze ((136 : usize))
        (Shake256Xof.state self)
        out);
    let self : Shake256Xof := {self with state := tmp0};
    let out : (RustSlice u8) := tmp1;
    let _ := rust_primitives.hax.Tuple0.mk;
    (pure (rust_primitives.hax.Tuple2.mk self out))

--  Create a new SHAKE-128 state object.
@[spec]
def shake128_init (_ : rust_primitives.hax.Tuple0) :
    RustM libcrux_iot_sha3.portable.KeccakState := do
  (pure (libcrux_iot_sha3.portable.KeccakState.mk
    (state := (← (libcrux_iot_sha3.state.Impl.new
      rust_primitives.hax.Tuple0.mk)))))

--  Absorb
@[spec]
def shake128_absorb_final
    (s : libcrux_iot_sha3.portable.KeccakState)
    (data0 : (RustSlice u8)) :
    RustM libcrux_iot_sha3.portable.KeccakState := do
  let s : libcrux_iot_sha3.portable.KeccakState :=
    {s
    with state := (← (libcrux_iot_sha3.keccak.absorb_final
      ((168 : usize))
      ((31 : u8))
      (libcrux_iot_sha3.portable.KeccakState.state s)
      data0
      (0 : usize)
      (← (core_models.slice.Impl.len u8 data0))))};
  (pure s)

--  Perform four rounds of the keccak permutation functions
@[spec]
def keccakf1660_4rounds (s : libcrux_iot_sha3.portable.KeccakState) :
    RustM libcrux_iot_sha3.portable.KeccakState := do
  let s : libcrux_iot_sha3.portable.KeccakState :=
    {s
    with state := (← (libcrux_iot_sha3.keccak.keccakf1600_4rounds ((0 : usize))
      (libcrux_iot_sha3.portable.KeccakState.state s)))};
  (pure s)

--  Squeeze three blocks
@[spec]
def shake128_squeeze_first_three_blocks
    (s : libcrux_iot_sha3.portable.KeccakState)
    (out0 : (RustSlice u8)) :
    RustM
    (rust_primitives.hax.Tuple2
      libcrux_iot_sha3.portable.KeccakState
      (RustSlice u8))
    := do
  let ⟨tmp0, tmp1⟩ ←
    (libcrux_iot_sha3.keccak.squeeze_first_three_blocks ((168 : usize))
      (libcrux_iot_sha3.portable.KeccakState.state s)
      out0);
  let s : libcrux_iot_sha3.portable.KeccakState := {s with state := tmp0};
  let out0 : (RustSlice u8) := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure (rust_primitives.hax.Tuple2.mk s out0))

--  Squeeze five blocks
@[spec]
def shake128_squeeze_first_five_blocks
    (s : libcrux_iot_sha3.portable.KeccakState)
    (out0 : (RustSlice u8)) :
    RustM
    (rust_primitives.hax.Tuple2
      libcrux_iot_sha3.portable.KeccakState
      (RustSlice u8))
    := do
  let ⟨tmp0, tmp1⟩ ←
    (libcrux_iot_sha3.keccak.squeeze_first_five_blocks ((168 : usize))
      (libcrux_iot_sha3.portable.KeccakState.state s)
      out0);
  let s : libcrux_iot_sha3.portable.KeccakState := {s with state := tmp0};
  let out0 : (RustSlice u8) := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure (rust_primitives.hax.Tuple2.mk s out0))

--  Squeeze another block
@[spec]
def shake128_squeeze_next_block
    (s : libcrux_iot_sha3.portable.KeccakState)
    (out0 : (RustSlice u8)) :
    RustM
    (rust_primitives.hax.Tuple2
      libcrux_iot_sha3.portable.KeccakState
      (RustSlice u8))
    := do
  let ⟨tmp0, tmp1⟩ ←
    (libcrux_iot_sha3.keccak.squeeze_next_block ((168 : usize))
      (libcrux_iot_sha3.portable.KeccakState.state s)
      out0);
  let s : libcrux_iot_sha3.portable.KeccakState := {s with state := tmp0};
  let out0 : (RustSlice u8) := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure (rust_primitives.hax.Tuple2.mk s out0))

--  Create a new SHAKE-256 state object.
@[spec]
def shake256_init (_ : rust_primitives.hax.Tuple0) :
    RustM libcrux_iot_sha3.portable.KeccakState := do
  (pure (libcrux_iot_sha3.portable.KeccakState.mk
    (state := (← (libcrux_iot_sha3.state.Impl.new
      rust_primitives.hax.Tuple0.mk)))))

--  Absorb some data for SHAKE-256 for the last time
@[spec]
def shake256_absorb_final
    (s : libcrux_iot_sha3.portable.KeccakState)
    (data : (RustSlice u8)) :
    RustM libcrux_iot_sha3.portable.KeccakState := do
  let s : libcrux_iot_sha3.portable.KeccakState :=
    {s
    with state := (← (libcrux_iot_sha3.keccak.absorb_final
      ((136 : usize))
      ((31 : u8))
      (libcrux_iot_sha3.portable.KeccakState.state s)
      data
      (0 : usize)
      (← (core_models.slice.Impl.len u8 data))))};
  (pure s)

--  Squeeze the first SHAKE-256 block
@[spec]
def shake256_squeeze_first_block
    (s : libcrux_iot_sha3.portable.KeccakState)
    (out : (RustSlice u8)) :
    RustM
    (rust_primitives.hax.Tuple2
      libcrux_iot_sha3.portable.KeccakState
      (RustSlice u8))
    := do
  let ⟨tmp0, out1⟩ := (libcrux_iot_sha3.portable.KeccakState.state s);
  let s : libcrux_iot_sha3.portable.KeccakState := {s with state := tmp0};
  let out : (RustSlice u8) ←
    (libcrux_iot_sha3.keccak.squeeze_first_block ((136 : usize)) out1 out);
  (pure (rust_primitives.hax.Tuple2.mk s out))

--  Squeeze the next SHAKE-256 block
@[spec]
def shake256_squeeze_next_block
    (s : libcrux_iot_sha3.portable.KeccakState)
    (out : (RustSlice u8)) :
    RustM
    (rust_primitives.hax.Tuple2
      libcrux_iot_sha3.portable.KeccakState
      (RustSlice u8))
    := do
  let ⟨tmp0, tmp1⟩ ←
    (libcrux_iot_sha3.keccak.squeeze_next_block ((136 : usize))
      (libcrux_iot_sha3.portable.KeccakState.state s)
      out);
  let s : libcrux_iot_sha3.portable.KeccakState := {s with state := tmp0};
  let out : (RustSlice u8) := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure (rust_primitives.hax.Tuple2.mk s out))

end libcrux_iot_sha3.portable.incremental

