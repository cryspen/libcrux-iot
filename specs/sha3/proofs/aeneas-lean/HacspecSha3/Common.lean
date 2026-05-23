/-
  # `HacspecSha3/Common.lean` — shared `core_models.*` shims.

  Hosts the `core_models.*` instances and helpers that were previously
  duplicated across `HacspecSha3/Missing.lean`,
  `LibcruxIotSha3/Extraction/Missing.lean`, and
  `HacspecMlKem/Missing.lean`. Importing both spec and impl trees in
  a single module (needed by Layer M / M.4 / Phase-5 functional
  upgrades) requires these shims live in exactly one place.

  Canonical bodies:

  - **Usize.Insts.Core_modelsFmtDisplay** — no-op format stub (only
    appears in dead `/- ... -/` panic-path comments in extraction).
  - **Shared0T.Insts.Core_modelsFmtDebug** — passthrough.
  - **I32.Insts.Core_modelsIterRangeStep** — real-behavior step
    (matches the Sha3 prior; ml-kem extraction doesn't iterate over
    I32 ranges so the choice is moot at use sites).
  - **cmRangeToUsizeToAeneas** + **RangeToUsize.SliceIndex** —
    RangeTo-faithful (Sha3) variant. Callers dispatch via the
    trait method name so the choice of impl is moot.

  Imports of this file: `HacspecSha3/Missing.lean` includes it; both
  downstream Missing.lean files (LibcruxIotSha3, HacspecMlKem) get it
  transitively via their existing `import HacspecSha3[.Missing]`.
-/
import Aeneas
import CoreModels

open Aeneas Aeneas.Std Result

noncomputable section

namespace core_models

/-- `Display` for `Usize`. No-op stub; only referenced inside
    `/- ... -/` block comments in extraction (panic-path format
    strings that `fail panic` replaced). -/
@[reducible] def Usize.Insts.Core_modelsFmtDisplay : core_models.fmt.Display Usize :=
  { fmt := fun _ f => ok (core_models.result.Result.Ok (), f) }

/-- `Debug` for `&T` — passthrough to the underlying `Debug T`. -/
@[reducible] def Shared0T.Insts.Core_modelsFmtDebug
    {T : Type} (d : fmt.Debug T) : fmt.Debug T := d

/-- `Step I32` for I32 ranges. Real-behavior body (matches
    `LibcruxIotSha3/Extraction/Missing.lean`'s prior). The ml-kem
    extraction never iterates I32 ranges so callers see only the
    trait method names; the impl choice is moot. -/
def I32.Insts.Core_modelsIterRangeStep : core_models.iter.range.Step I32 := {
  cloneInst       := { clone := fun x => Aeneas.Std.Result.ok x }
  partialOrdInst  := {
    PartialEqInst := { eq := fun x y => ok (x == y) }
    partial_cmp := fun x y =>
      ok (core_models.option.Option.Some
        (match compare x.val y.val with
        | .lt => core_models.cmp.Ordering.Less
        | .eq => core_models.cmp.Ordering.Equal
        | .gt => core_models.cmp.Ordering.Greater))
  }
  steps_between   :=
    λ start end_ =>
      if h: start > end_ then ok ⟨ 0#usize, none ⟩ else
        let steps := Usize.ofNatCore (end_.val - start.val).toNat (by scalar_tac)
        ok ⟨ steps, some steps ⟩
  forward_checked :=
    λ start n => ok (Option.ofResult (IScalar.tryMk .I32 (start.val + (n.val : Int))))
  backward_checked :=
    λ start n => ok (Option.ofResult (IScalar.tryMk .I32 (start.val - (n.val : Int))))
}

/-- No-op `Arguments.new` stub. The polymorphic variant satisfies
    both call patterns (Sha3 expects monomorphic `Array U8` /
    `Array fmt.rt.Argument`; ml-kem extraction uses the same
    shape under the polymorphic abstraction). Only referenced
    inside `/- ... -/` block comments in extraction. -/
def fmt.Arguments.new {N1 N2 : Aeneas.Std.Usize} {T1 T2 : Type}
    (_pieces : Aeneas.Std.Array T1 N1) (_args : Aeneas.Std.Array T2 N2) :
    Aeneas.Std.Result fmt.Arguments :=
  Aeneas.Std.Result.ok ()

/-- `Formatter.write_str` — taking `Aeneas.Std.Str` (matches live
    callers in LibcruxIotSha3 `Algorithm.Insts.Core_modelsFmtDebug.fmt`).
    No-op body; the formatter state is `Unit` so writes carry no
    information. -/
def fmt.Formatter.write_str
  (f : fmt.Formatter) (_ : Aeneas.Std.Str) :
  Aeneas.Std.Result (result.Result Unit fmt.Error × fmt.Formatter) :=
  Aeneas.Std.Result.ok (.Ok (), f)

/-- `Array<T, N>::as_slice`. Routes to Aeneas's `Array.to_slice`. -/
def array.Array.as_slice {T : Type} {N : Aeneas.Std.Usize}
    (a : Aeneas.Std.Array T N) : Aeneas.Std.Result (Aeneas.Std.Slice T) :=
  Aeneas.Std.Result.ok (Aeneas.Std.Array.to_slice a)

/-- `Slice::split_at` — routes to Aeneas's `core.slice.Slice.split_at`. -/
def slice.Slice.split_at {T : Type} (s : Aeneas.Std.Slice T) (mid : Aeneas.Std.Usize) :
    Aeneas.Std.Result (Aeneas.Std.Slice T × Aeneas.Std.Slice T) :=
  Aeneas.Std.core.slice.Slice.split_at s mid

/-- `Slice::chunks_exact` — bundles the chunk size + slice into a
    `ChunksExact` iterator state. Stub returning `panic` since the
    iterator implementation is opaque to current callers. -/
def slice.Slice.chunks_exact {T : Type}
    (_s : Aeneas.Std.Slice T) (_cs : Aeneas.Std.Usize) :
    Aeneas.Std.Result (slice.iter.ChunksExact T) :=
  Aeneas.Std.Result.fail Aeneas.Std.Error.panic

/-- `Iterator::next` for `ChunksExact<T>` (shared-slice item type).
    Stub returning `(None, iter)` — terminates iteration immediately. -/
def slice.iter.ChunksExact.Insts.Core_modelsIterTraitsIteratorIteratorSharedASlice.next
    {T : Type} (iter : slice.iter.ChunksExact T) :
    Aeneas.Std.Result ((option.Option (Aeneas.Std.Slice T)) × slice.iter.ChunksExact T) :=
  Aeneas.Std.Result.ok (option.Option.None, iter)

/-- `RangeTo Usize → RangeTo Usize` identity bridge (preserves the
    Rust type-level distinction between `RangeTo` and `Range`). -/
def cmRangeToUsizeToAeneas (r : ops.range.RangeTo Aeneas.Std.Usize) :
    Aeneas.Std.core.ops.range.RangeTo Aeneas.Std.Usize :=
  { «end» := r.«end» }

/-- `SliceIndex` for `RangeTo Usize` (`s[..end]`). Forwards to
    Aeneas's `SliceIndexRangeToUsizeSlice.*`. -/
@[reducible] def ops.range.RangeToUsize.Insts.Core_modelsSliceIndexSliceIndexSliceSlice
  (T : Type) : Aeneas.Std.core.slice.index.SliceIndex
    (ops.range.RangeTo Aeneas.Std.Usize) (Aeneas.Std.Slice T) (Aeneas.Std.Slice T) :=
  { sealedInst := {}
    get := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeToUsizeSlice.get (cmRangeToUsizeToAeneas r) s
    get_mut := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeToUsizeSlice.get_mut (cmRangeToUsizeToAeneas r) s
    get_unchecked := fun _ _ => Aeneas.Std.Result.fail Aeneas.Std.Error.undef
    get_unchecked_mut := fun _ _ => Aeneas.Std.Result.fail Aeneas.Std.Error.undef
    index := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeToUsizeSlice.index (cmRangeToUsizeToAeneas r) s
    index_mut := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeToUsizeSlice.index_mut (cmRangeToUsizeToAeneas r) s }

end core_models

end
