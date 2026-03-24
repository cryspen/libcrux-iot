import Hax

/- ## Libcrux secrets -/
def libcrux_secrets.traits.Classify.classify (α : Type) (x : α) : RustM α := pure x

class libcrux_secrets.int.CastOps (α : Type) where
  as_u64 (α) : α → RustM u64
  as_u32 (α) : α → RustM u32

instance : libcrux_secrets.int.CastOps u32 where
  as_u32 x := pure x
  as_u64 x := pure x.toUInt64

instance : libcrux_secrets.int.CastOps u64 where
  as_u32 x := pure x.toUInt32
  as_u64 x := pure x

/- ## Index trait -/

instance [core_models.ops.index.Index.AssociatedTypes α β] [core_models.ops.index.Index α β] :
  GetElemResult α β (core_models.ops.index.Index.AssociatedTypes.Output α β) := {
    getElemResult xs i := core_models.ops.index.Index.index _ _ xs i
  }


/- ## Update at range -/
class rust_primitives.hax.monomorphized_update_at (α : Type) where
  update_at_range : α → core_models.ops.range.Range usize → RustSlice u8 → RustM α
  update_at_range_from : α → core_models.ops.range.RangeFrom usize → RustSlice u8 → RustM α
  update_at_range_to : α → core_models.ops.range.RangeTo usize → RustSlice u8 → RustM α
  update_at_range_full : α → core_models.ops.range.RangeFull → RustSlice u8 → RustM α

instance : rust_primitives.hax.monomorphized_update_at (RustArray u8 n) where
  update_at_range a r b :=
    let s := r.start.toNat
    let e := r._end.toNat
    if h : s ≤ e && e ≤ n.toNat && b.val.size == e - s then
      let front := a.toVec.toArray.extract 0 s
      let back := a.toVec.toArray.extract e n.toNat
      pure ⟨⟨front ++ b.val ++ back, by grind⟩⟩
    else
      .fail .arrayOutOfBounds
  update_at_range_from a r b :=
    let s := r.start.toNat
    if h : s ≤ n.toNat && b.val.size == n.toNat - s then
      let front := a.toVec.toArray.extract 0 s
      pure ⟨⟨front ++ b.val, by grind⟩⟩
    else
      .fail .arrayOutOfBounds
  update_at_range_to a r b :=
    let e := r._end.toNat
    if h : e ≤ n.toNat && b.val.size == e then
      let back := a.toVec.toArray.extract e n.toNat
      pure ⟨⟨b.val ++ back, by grind⟩⟩
    else
      .fail .arrayOutOfBounds
  update_at_range_full a _ b :=
    if h : b.val.size == n.toNat then
      pure ⟨⟨b.val, by grind⟩⟩
    else
      .fail .arrayOutOfBounds

instance : rust_primitives.hax.monomorphized_update_at (RustSlice u8) where
  update_at_range a r b :=
    let s := r.start.toNat
    let e := r._end.toNat
    if h : s ≤ e && e ≤ a.val.size && b.val.size == e - s then
      let front := a.val.extract 0 s
      let back := a.val.extract e a.val.size
      pure ⟨front ++ b.val ++ back, by grind [a.size_lt_usizeSize]⟩
    else
      .fail .arrayOutOfBounds
  update_at_range_from a r b :=
    let s := r.start.toNat
    if h : s ≤ a.val.size && b.val.size == a.val.size - s then
      let front := a.val.extract 0 s
      pure ⟨front ++ b.val, by grind [a.size_lt_usizeSize]⟩
    else
      .fail .arrayOutOfBounds
  update_at_range_to a r b :=
    let e := r._end.toNat
    if h : e ≤ a.val.size && b.val.size == e then
      let back := a.val.extract e a.val.size
      pure ⟨b.val ++ back, by grind [a.size_lt_usizeSize]⟩
    else
      .fail .arrayOutOfBounds
  update_at_range_full a _ b :=
    if h : b.val.size == a.val.size then
      pure ⟨b.val, by grind [a.size_lt_usizeSize]⟩
    else
      .fail .arrayOutOfBounds

/- ## Making slices -/

instance : GetElemResult (RustArray u8 n) (core_models.ops.range.RangeFrom usize) (RustSlice u8) where
  getElemResult xs i :=
    let s := i.start.toNat
    if h : s ≤ n.toNat then
      pure ⟨xs.toVec.toArray.extract s n.toNat, by grind [USize64.toNat_lt_size]⟩
    else
      .fail .arrayOutOfBounds

instance : GetElemResult (RustSlice u8) (core_models.ops.range.RangeFrom usize) (RustSlice u8) where
  getElemResult xs i :=
    let s := i.start.toNat
    if h : s ≤ xs.val.size then
      pure ⟨xs.val.extract s xs.val.size, by grind [xs.size_lt_usizeSize]⟩
    else
      .fail .arrayOutOfBounds

instance : GetElemResult (RustSlice u8) (core_models.ops.range.RangeTo usize) (RustSlice u8) where
  getElemResult xs i :=
    let e := i._end.toNat
    if h : e ≤ xs.val.size then
      pure ⟨xs.val.extract 0 e, by grind [xs.size_lt_usizeSize]⟩
    else
      .fail .arrayOutOfBounds

instance : GetElemResult (RustArray u8 n) (core_models.ops.range.RangeFull) (RustSlice u8) where
  getElemResult xs _ :=
    pure ⟨xs.toVec.toArray, by grind [USize64.toNat_lt_size]⟩

instance : GetElemResult (RustSlice u8) (core_models.ops.range.RangeFull) (RustSlice u8) where
  getElemResult xs _ := pure xs



/- ## Missing core model definition -/
def core_models.num.Impl_8.MAX : u32 := -1


/- ## For loops for signed integers
See https://github.com/cryspen/hax/issues/1783
-/

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
