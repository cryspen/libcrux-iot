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
