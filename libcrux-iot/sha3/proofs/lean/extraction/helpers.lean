import Hax

def libcrux_secrets.traits.Classify.classify (α : Type) : α → RustM α := sorry
def libcrux_secrets.int.CastOps.as_u64 (α : Type) : α → RustM u64 := sorry
instance : GetElemResult Lane2U32 usize u32 := sorry
def libcrux_secrets.int.CastOps.as_u32 (α : Type) : α → RustM u32 := sorry


class core_models.ops.index.IndexMut.AssociatedTypes (A B : Type) where

class core_models.ops.index.IndexMut (A B : Type) where
  index_mut : A → B → RustM u32

def rust_primitives.hax.monomorphized_update_at.update_at_range_from :
  RustArray u8 RATE → core_models.ops.range.RangeFrom usize → RustSlice u8 → RustM (RustArray u8 RATE) := sorry

def rust_primitives.hax.monomorphized_update_at.update_at_range :
  RustArray u8 RATE → core_models.ops.range.Range usize → RustSlice u8 → RustM (RustArray u8 RATE) := sorry

instance : GetElemResult (RustArray u8 RATE) (core_models.ops.range.RangeFrom usize) (RustSlice u8) := sorry
instance :  GetElemResult (RustSlice u8) (core_models.ops.range.RangeFrom usize) (RustSlice u8) := sorry

instance : GetElemResult (RustSlice u8) (core_models.ops.range.RangeTo usize) (RustSlice u8) := sorry

def core_models.num.Impl_8.MAX : u32 := sorry

open Std.Do

def Int32.fold_range {α : Type}
    (s e : Int32)
    (inv : α -> Int32 -> RustM Prop)
    (init: α)
    (body : α -> Int32 -> RustM α)
    (pureInv: {i : α -> Int32 -> Prop // ∀ a b, ⦃⌜ True ⌝⦄ inv a b ⦃⇓ r => ⌜ r = (i a b) ⌝⦄})
    : RustM α := do
    if s < e
    then fold_range (s + 1) e inv (← body init s) body pureInv
    else pure init
termination_by (e.toInt - s.toInt).toNat
decreasing_by
  have : (s + 1).toInt = s.toInt + 1 := by grind
  grind

@[spec]
instance : @rust_primitives.hax.folds Int32 where
  fold_range := Int32.fold_range
  fold_range_return := sorry
