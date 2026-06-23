-- Hand-written stubs for symbols missing in Aeneas / rust-core-models.
--
-- The ML-DSA impl uses `libcrux_secrets::I32` coefficients and `I64`
-- montgomery arithmetic, so the generated `Funs.lean` references
-- `libcrux_secrets.*` integer-cast + classify/declassify functions. It also
-- routes a couple of helper functions (`vector_infinity_norm_exceeds`,
-- `to_i32_array`) through `core.slice.Slice.iter` / `Enumerate`, and the
-- per-vector serialize helpers through `core.slice.Slice.copy_from_slice` /
-- `core.Slice.Insts.CoreOpsIndexIndex.index`.
--
-- The ML-KEM tree gets the `core.*` slice ops for free from its
-- `HacspecSha3.Missing` dependency; ML-DSA does not depend on Hacspec*, so we
-- mirror those `CoreModels.core.*` defs here. The `slice.iter.Iter`/`Enumerate`
-- iterator wiring is mirrored from the `array.iter.IntoIter` instance already
-- in `CoreModels` (both are `rust_primitives.sequence.Seq`).
import Aeneas
import CoreModels

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Result

noncomputable section

/-! ## `core.*` slice / index / iterator ops (mirrored from `HacspecSha3.Missing`
    + the `CoreModels` `array.iter.IntoIter` instance). -/

namespace CoreModels.core

/-! ### Generic `Index`/`IndexMut` wrappers that the `-core-models-lib`
extraction expects. They take an Aeneas `core.slice.index.SliceIndex` instance
and delegate to Aeneas's native implementations. -/

def Slice.Insts.CoreOpsIndexIndex
  {T I O : Type} (inst : Aeneas.Std.core.slice.index.SliceIndex I (Slice T) O) :
  Aeneas.Std.core.slice.index.SliceIndex I (Slice T) O := inst

def Slice.Insts.CoreOpsIndexIndexMut
  {T I O : Type} (inst : Aeneas.Std.core.slice.index.SliceIndex I (Slice T) O) :
  Aeneas.Std.core.slice.index.SliceIndex I (Slice T) O := inst

def Slice.Insts.CoreOpsIndexIndex.index
  {T I O : Type}
  (inst : Aeneas.Std.core.slice.index.SliceIndex I (Slice T) O)
  (s : Slice T) (i : I) : Result O :=
  Aeneas.Std.core.slice.index.Slice.index inst s i

def Slice.Insts.CoreOpsIndexIndexMut.index_mut
  {T I O : Type}
  (inst : Aeneas.Std.core.slice.index.SliceIndex I (Slice T) O)
  (s : Slice T) (i : I) : Result (O × (O → Slice T)) :=
  Aeneas.Std.core.slice.index.Slice.index_mut inst s i

def Array.Insts.CoreOpsIndexIndex.index
  {T I O : Type} {N : Usize}
  (inst : Aeneas.Std.core.slice.index.SliceIndex I (Slice T) O)
  (arr : Array T N) (i : I) : Result O :=
  Aeneas.Std.core.slice.index.Slice.index inst (Array.to_slice arr) i

def Array.Insts.CoreOpsIndexIndexMut.index_mut
  {T I O : Type} {N : Usize}
  (inst : Aeneas.Std.core.slice.index.SliceIndex I (Slice T) O)
  (arr : Array T N) (i : I) : Result (O × (O → Array T N)) := do
  let (s, to_arr) := Array.to_slice_mut arr
  let (out, to_slice) ← Aeneas.Std.core.slice.index.Slice.index_mut inst s i
  ok (out, fun o => to_arr (to_slice o))

/-! ### Bridge from `RangeUsize` to Aeneas's native `SliceIndex` instance. -/

def ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice (T : Type) :
    Aeneas.Std.core.slice.index.SliceIndex
      (CoreModels.core.ops.range.Range Usize) (Slice T) (Slice T) :=
  let toAeneas (r : CoreModels.core.ops.range.Range Usize) :
      Aeneas.Std.core.ops.range.Range Usize :=
    { start := r.start, «end» := r.«end» }
  { sealedInst := {}
    get := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.get (toAeneas r) s
    get_mut := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.get_mut (toAeneas r) s
    get_unchecked := fun _ _ => Result.fail Error.undef
    get_unchecked_mut := fun _ _ => Result.fail Error.undef
    index := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.index (toAeneas r) s
    index_mut := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.index_mut (toAeneas r) s }

/-! ### `core.result.Result.unwrap` model — converts the model
`result.Result T E` into an Aeneas `Result T`, panicking on `Err`. -/

def result.Result.unwrap
    {T E : Type} (_dbg : CoreModels.core.fmt.Debug E)
    (r : CoreModels.core.result.Result T E) : Aeneas.Std.Result T :=
  match r with
  | .Ok x => Aeneas.Std.Result.ok x
  | .Err _ => Aeneas.Std.Result.fail Aeneas.Std.Error.panic

/-! ### `core.slice.Slice.copy_from_slice` — panics on length mismatch. -/

def slice.Slice.copy_from_slice
    {T : Type} (_cpy : CoreModels.core.marker.Copy T)
    (dst : Aeneas.Std.Slice T) (src : Aeneas.Std.Slice T) :
    Aeneas.Std.Result (Aeneas.Std.Slice T) :=
  if Aeneas.Std.Slice.len dst = Aeneas.Std.Slice.len src then
    Aeneas.Std.Result.ok src
  else Aeneas.Std.Result.fail Aeneas.Std.Error.panic

/-! ### `core.slice.Slice.iter` + the `slice.iter.Iter` iterator instance.

`slice.iter.Iter T = rust_primitives.sequence.Seq T = Aeneas.Std.Slice T`.
`Slice.iter` is `seq_from_slice` (identity); the `Iterator` instance's `.next`
and the `.enumerate` adapter mirror the `array.iter.IntoIter` versions already
in `CoreModels`. -/

def slice.Slice.iter
  {T : Type} (s : Slice T) : Result (slice.iter.Iter T) :=
  rust_primitives.sequence.seq_from_slice s

def slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next
  {T : Type} (self : slice.iter.Iter T) :
  Result ((option.Option T) × (slice.iter.Iter T))
  := do
  let i ← rust_primitives.sequence.seq_len self
  if i = 0#usize
  then ok (option.Option.None, self)
  else
    let (res, s) ← rust_primitives.sequence.seq_remove self 0#usize
    ok (option.Option.Some res, s)

@[reducible]
def slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT (T : Type) :
  iter.traits.iterator.Iterator (slice.iter.Iter T) T :=
  { next := slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next }

def slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.enumerate
  {T : Type} (self : slice.iter.Iter T) :
  Result (iter.adapters.enumerate.Enumerate (slice.iter.Iter T)) :=
  ok { iter := self, count := 0#usize }

end CoreModels.core

/-! ## `libcrux_secrets.*` integer-cast + classify/declassify stubs.
    `libcrux_secrets`-functions are not part of the extraction; we map
    them to identity functions on the underlying scalar types, written in the
    upstream `declassify → cast → classify` shape so downstream proofs can
    unfold the chain. -/

namespace libcrux_secrets.traits.Classify.Blanket
def classify {T : Type} (a : T) : Aeneas.Std.Result T := ok a
end libcrux_secrets.traits.Classify.Blanket

namespace libcrux_secrets.traits.Declassify.Blanket
def declassify {T : Type} (a : T) : Aeneas.Std.Result T := ok a
end libcrux_secrets.traits.Declassify.Blanket

namespace libcrux_secrets

/-- `I64 → U64` cast (`montgomery_reduce_element`'s leading `as_u64`). -/
def I64.Insts.Libcrux_secretsIntCastOps.as_u64 (x : Std.I64) : Result Std.U64 := do
  let i ← traits.Declassify.Blanket.declassify x
  let i1 ← lift (Std.IScalar.hcast .U64 i)
  traits.Classify.Blanket.classify i1

/-- `I64 → I32` cast (montgomery reduction's trailing narrowings). -/
def I64.Insts.Libcrux_secretsIntCastOps.as_i32 (x : Std.I64) : Result Std.I32 := do
  let i ← traits.Declassify.Blanket.declassify x
  let i1 ← lift (Std.IScalar.cast .I32 i)
  traits.Classify.Blanket.classify i1

/-- `U64 → I32` cast (montgomery reduction's `k` extraction). -/
def U64.Insts.Libcrux_secretsIntCastOps.as_i32 (x : Std.U64) : Result Std.I32 := do
  let i ← traits.Declassify.Blanket.declassify x
  let i1 ← lift (Std.UScalar.hcast .I32 i)
  traits.Classify.Blanket.classify i1

/-- `I32 → I64` cast (montgomery multiply widening). -/
def I32.Insts.Libcrux_secretsIntCastOps.as_i64 (x : Std.I32) : Result Std.I64 := do
  let i ← traits.Declassify.Blanket.declassify x
  let i1 ← lift (Std.IScalar.cast .I64 i)
  traits.Classify.Blanket.classify i1

/-! `Scalar` marker trait (carries no methods we use); `PUnit` for shape, and a
    `declassify_ref` on a shared reference — no-op identity (used by
    `to_coefficient_array` on `value.values : Array Std.I32 8`). -/

@[reducible] def traits.Scalar (_Self : Type) : Type := PUnit
@[reducible] def I32.Insts.Libcrux_secretsTraitsScalar : traits.Scalar Std.I32 := PUnit.unit

/-- `declassify_ref` on a shared reference — no-op identity. Kept generic. -/
def SharedAT.Insts.Libcrux_secretsTraitsDeclassifyRefSharedAT.declassify_ref
    {T : Type} (a : T) : Aeneas.Std.Result T := ok a

end libcrux_secrets

end
