/- # `HacspecMlKem.Missing` — hand-written stubs for symbols the
   current rust-core-models pin (`b67ccf1`) doesn't define.

   Inherits the common stubs (slice/array index, `copy_from_slice`,
   `Result.unwrap`, `Range`/`RangeFrom` SliceIndex, `TryFromSliceError`
   Debug) from `HacspecSha3.Missing` via the `import HacspecSha3`
   below. The block under "UPSTREAM-TO-rust-core-models" is what
   ml-kem specifically needs on top: `RangeTo` SliceIndex,
   `SharedAArray` try_from, `Try` branch/from_residual, `Slice.split_at`,
   `chunks_exact`, comparison/format/iterator instances. -/
import Aeneas
import CoreModels
import HacspecSha3

open Aeneas Aeneas.Std Result

noncomputable section

namespace core_models

/-! ============================================================
    # UPSTREAM-TO-rust-core-models section

    Each instance / function below is a candidate to lift into
    `cryspen/rust-core-models` (the package providing
    `CoreModels.{Funs,Types,FunsPrologue,FunsExternal}`).
    They are stubbed here so that ml-kem spec extraction compiles
    against the current pin (`b67ccf1`), but the natural home is
    upstream alongside the existing `cmp.PartialEq` / `Step`
    instances in `FunsPrologue.lean`.

    The trait *structures* (`cmp.PartialEq`, `cmp.Ord`, `fmt.Display`,
    `fmt.Debug`, `slice.iter.ChunksExact`, `ops.control_flow.ControlFlow`,
    `convert.Infallible`, `fmt.Arguments = Unit`, `fmt.Formatter = Unit`)
    already exist in `CoreModels.Types`; we only add the per-type
    instances and a handful of missing functions.

    Order matches the failure inventory observed during ml-kem spec
    extraction (`SKIP_VERSION_CHECK=1 ./hax_aeneas.py` then `lake build`).
    ============================================================ -/

/-- `SliceIndex` instance for `RangeTo<usize>` indexing into `&[T]`.
    Mirror of the existing `Range` / `RangeFrom` variants in
    `HacspecSha3.Missing`; the `RangeTo { end }` form translates to
    `Range { start := 0, end }`. -/
def cmRangeToUsizeToAeneas (r : ops.range.RangeTo Aeneas.Std.Usize) :
    Aeneas.Std.core.ops.range.Range Aeneas.Std.Usize :=
  { start := 0#usize, «end» := r.«end» }

@[reducible] def ops.range.RangeToUsize.Insts.Core_modelsSliceIndexSliceIndexSliceSlice
  (T : Type) : Aeneas.Std.core.slice.index.SliceIndex
    (ops.range.RangeTo Aeneas.Std.Usize) (Aeneas.Std.Slice T) (Aeneas.Std.Slice T) :=
  { sealedInst := {}
    get := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.get (cmRangeToUsizeToAeneas r) s
    get_mut := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.get_mut (cmRangeToUsizeToAeneas r) s
    get_unchecked := fun _ _ => Aeneas.Std.Result.fail Aeneas.Std.Error.undef
    get_unchecked_mut := fun _ _ => Aeneas.Std.Result.fail Aeneas.Std.Error.undef
    index := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.index (cmRangeToUsizeToAeneas r) s
    index_mut := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.index_mut (cmRangeToUsizeToAeneas r) s }

/-- `SliceIndex` for `RangeFull` (`s[..]`). The full slice is just `s`. -/
def cmRangeFullToAeneas {T : Type} (_r : ops.range.RangeFull)
    (s : Aeneas.Std.Slice T) :
    Aeneas.Std.core.ops.range.Range Aeneas.Std.Usize :=
  { start := 0#usize, «end» := Aeneas.Std.Slice.len s }

@[reducible] def ops.range.RangeFull.Insts.Core_modelsSliceIndexSliceIndexSliceSlice
  (T : Type) : Aeneas.Std.core.slice.index.SliceIndex
    ops.range.RangeFull (Aeneas.Std.Slice T) (Aeneas.Std.Slice T) :=
  { sealedInst := {}
    get := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.get (cmRangeFullToAeneas r s) s
    get_mut := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.get_mut (cmRangeFullToAeneas r s) s
    get_unchecked := fun _ _ => Aeneas.Std.Result.fail Aeneas.Std.Error.undef
    get_unchecked_mut := fun _ _ => Aeneas.Std.Result.fail Aeneas.Std.Error.undef
    index := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.index (cmRangeFullToAeneas r s) s
    index_mut := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.index_mut (cmRangeFullToAeneas r s) s }

/-- `TryFrom<&[T]>` for `[T; N]`. Routes to Aeneas's
    `core.array.TryFromSharedArraySlice.try_from`. -/
def SharedAArray.Insts.Core_modelsConvertTryFromSharedASliceTryFromSliceError.try_from
    {T : Type} (N : Aeneas.Std.Usize) (s : Aeneas.Std.Slice T) :
    Aeneas.Std.Result (result.Result (Aeneas.Std.Array T N) array.TryFromSliceError) :=
  if h: s.len = N then
    Aeneas.Std.Result.ok (result.Result.Ok ⟨s.val, by scalar_tac⟩)
  else
    Aeneas.Std.Result.ok (result.Result.Err ())

/-- `Try::branch` for `Result<T, E>` (residual = `Result<Infallible, E>`).
    The `?`-operator desugar — branch is the "is this Ok or Err" split. -/
def result.Result.Insts.Core_modelsOpsTry_traitTryTResultInfallibleE.branch
    {T E : Type} (r : result.Result T E) :
    Aeneas.Std.Result (ops.control_flow.ControlFlow (result.Result convert.Infallible E) T) :=
  match r with
  | .Ok x => Aeneas.Std.Result.ok (.Continue x)
  | .Err e => Aeneas.Std.Result.ok (.Break (.Err e))

/-- `FromResidual::from_residual` for `Result<T, F>` from residual
    `Result<Infallible, E>` via `F: From<E>`. The other half of the
    `?`-operator desugar — lifts a Residual back into the carrier
    monad through the `From` instance.

    Aeneas-emitted call shape: `from_residual T FromInst residual`
    where `T` is the output value type (explicit) and `FromInst :
    convert.From F E` converts the residual's error to the
    surrounding function's error type. -/
def result.Result.Insts.Core_modelsOpsTry_traitFromResidualResultInfallibleE.from_residual
    {E F : Type} (T : Type) (FromInst : convert.From F E)
    (residual : result.Result convert.Infallible E) :
    Aeneas.Std.Result (result.Result T F) :=
  match residual with
  | .Err e => do
    let f ← FromInst.«from» e
    Aeneas.Std.Result.ok (.Err f)
  | .Ok _ => Aeneas.Std.Result.fail Aeneas.Std.Error.panic  -- Infallible has no inhabitants

/-- `Slice::split_at`. Routes to Aeneas's slice split. -/
def slice.Slice.split_at {T : Type} (s : Aeneas.Std.Slice T) (mid : Aeneas.Std.Usize) :
    Aeneas.Std.Result (Aeneas.Std.Slice T × Aeneas.Std.Slice T) :=
  Aeneas.Std.core.slice.Slice.split_at s mid

/-- `Slice::chunks_exact`. Bundles the chunk size + the slice into a
    `ChunksExact T`. Iteration is via `ChunksExact.…next` below.

    UPSTREAM-NOTE (blocking): `core_models.slice.iter.ChunksExact` is
    declared in rust-core-models's `Types.lean` with field
    `elements : Slice T` — and `Slice` there resolves to the reducible
    alias `core_models.slice.Slice T := T`, not to `Aeneas.Std.Slice T`.
    So the field literally expects a `T`, not a slice; we cannot
    construct a meaningful `ChunksExact T` from a real
    `Aeneas.Std.Slice T` value in this Lean encoding. Real fix
    requires a proper slice model upstream
    (e.g. `abbrev slice.Slice T := Aeneas.Std.Slice T`).
    Stubbed with `sorry`; only consumer in the current extraction is
    `ind_cca::public_key_modulus_check`. -/
def slice.Slice.chunks_exact {T : Type}
    (_s : Aeneas.Std.Slice T) (_cs : Aeneas.Std.Usize) :
    Aeneas.Std.Result (slice.iter.ChunksExact T) :=
  Aeneas.Std.Result.fail Aeneas.Std.Error.panic

/-- `Iterator::next` for `ChunksExact<T>` (item: shared `&[T]`).

    UPSTREAM-NOTE: this is a *minimal* stub that terminates the iterator
    immediately (returns `None`). It builds, but any spec consumer that
    relies on actual chunked iteration (e.g.
    `ind_cca::public_key_modulus_check`) will see a vacuously-true loop.
    Real semantics require `split_at(cs)` head/tail logic and a
    length-monus on `elements`. -/
def slice.iter.ChunksExact.Insts.Core_modelsIterTraitsIteratorIteratorSharedASlice.next
    {T : Type} (iter : slice.iter.ChunksExact T) :
    Aeneas.Std.Result ((option.Option (Aeneas.Std.Slice T)) × slice.iter.ChunksExact T) :=
  Aeneas.Std.Result.ok (option.Option.None, iter)

/-- `PartialEq<Bool>` for `Bool`. Mirror of the integer `PartialEq`
    instances already in `CoreModels.FunsPrologue`. -/
instance Bool.Insts.Core_modelsCmpPartialEqBool : cmp.PartialEq Bool Bool :=
  { eq := fun x y => Aeneas.Std.Result.ok (x == y) }

/-- `PartialOrd<U16>` for `U16`. -/
instance U16.Insts.Core_modelsCmpPartialOrdU16 : cmp.PartialOrd Aeneas.Std.U16 Aeneas.Std.U16 :=
  { PartialEqInst := U16.Insts.Core_modelsCmpPartialEqU16
    partial_cmp := fun x y => Aeneas.Std.Result.ok (option.Option.Some
      (match compare x.val y.val with
       | .lt => cmp.Ordering.Less
       | .eq => cmp.Ordering.Equal
       | .gt => cmp.Ordering.Greater)) }

/-- `Ord` for `U16`. -/
instance U16.Insts.Core_modelsCmpOrd : cmp.Ord Aeneas.Std.U16 :=
  { EqInst := { PartialEqInst := U16.Insts.Core_modelsCmpPartialEqU16 }
    PartialOrdInst := U16.Insts.Core_modelsCmpPartialOrdU16
    cmp := fun x y => Aeneas.Std.Result.ok
      (match compare x.val y.val with
       | .lt => cmp.Ordering.Less
       | .eq => cmp.Ordering.Equal
       | .gt => cmp.Ordering.Greater) }

/-- `Step` instance for `I32` ranges. Mirror of `StepUsize` in
    `CoreModels.FunsPrologue`. Range iteration over `0..n : i32`. -/
def iter.range.StepI32 : iter.range.Step Aeneas.Std.I32 :=
  { cloneInst       := { clone := fun x => Aeneas.Std.Result.ok x }
    partialOrdInst  := {
      PartialEqInst := { eq := fun x y => Aeneas.Std.Result.ok (x == y) }
      partial_cmp := fun x y => Aeneas.Std.Result.ok (option.Option.Some
        (match compare x.val y.val with
         | .lt => cmp.Ordering.Less
         | .eq => cmp.Ordering.Equal
         | .gt => cmp.Ordering.Greater))
    }
    steps_between := fun _ _ =>
      Aeneas.Std.Result.ok (0#usize, Option.none)
    forward_checked := fun cur step => do
      -- step is Usize; widen to I32 via UScalar.hcast (pure cast).
      let s := Aeneas.Std.UScalar.hcast .I32 step
      let n ← cur + s
      Aeneas.Std.Result.ok (Option.some n)
    backward_checked := fun cur step => do
      let s := Aeneas.Std.UScalar.hcast .I32 step
      let n ← cur - s
      Aeneas.Std.Result.ok (Option.some n) }

abbrev I32.Insts.Core_modelsIterRangeStep := iter.range.StepI32

/-- `Display` for `Usize`. No-op stub: `fmt.Formatter = Unit` so
    formatting carries no information; format sites are pure
    panic-path machinery. -/
instance Usize.Insts.Core_modelsFmtDisplay : fmt.Display Aeneas.Std.Usize :=
  { fmt := fun _ f => Aeneas.Std.Result.ok (result.Result.Ok (), f) }

/-- `Debug` for `&T`. Forwards to the underlying `Debug T`. -/
@[reducible] def Shared0T.Insts.Core_modelsFmtDebug
    {T : Type} (dbg : fmt.Debug T) : fmt.Debug T :=
  dbg

/-- `Debug` for `U16` — no-op format. -/
instance U16.Insts.Core_modelsFmtDebug : fmt.Debug Aeneas.Std.U16 :=
  { dbg_fmt := fun _ f => Aeneas.Std.Result.ok (result.Result.Ok (), f) }

/-- `PartialEq` for `&A` vs `&B` (sharing-marker variant). Used by
    `chunk != re_encoded` comparisons in `ind_cca.public_key_modulus_check`
    where both sides are slice references. Forwards to the underlying
    `PartialEq A B` instance. -/
def Shared1A.Insts.Core_modelsCmpPartialEqShared0B.ne
    {A B : Type} (inst : cmp.PartialEq A B) (a : A) (b : B) :
    Aeneas.Std.Result Bool := do
  let eq ← inst.eq a b
  Aeneas.Std.Result.ok (!eq)

/-- `PartialEq Slice<T> Slice<T>` from elementwise `PartialEq T T`.
    UPSTREAM-NOTE: stubbed to always-true; the only consumer in current
    extraction is `ind_cca.public_key_modulus_check`, a peripheral
    function. A proper instance needs `DecidableEq T` (which we'd derive
    from the inst's `.eq` lifted from Result Bool to a decidable
    predicate) or a recursive comparison over `.val`. -/
def Slice.Insts.Core_modelsCmpPartialEqSlice
    {T : Type} (_inst : cmp.PartialEq T T) :
    cmp.PartialEq (Aeneas.Std.Slice T) (Aeneas.Std.Slice T) :=
  { eq := fun _ _ => Aeneas.Std.Result.ok true }

/-- `Array::as_slice`. Routes to Aeneas's `Array.to_slice`. -/
def array.Array.as_slice {T : Type} {N : Aeneas.Std.Usize}
    (a : Aeneas.Std.Array T N) : Aeneas.Std.Result (Aeneas.Std.Slice T) :=
  Aeneas.Std.Result.ok (Aeneas.Std.Array.to_slice a)

/-- `fmt::Arguments::new` constructor. No-op since `fmt.Arguments = Unit`. -/
def fmt.Arguments.new {N1 N2 : Aeneas.Std.Usize} {T1 T2 : Type}
    (_pieces : Aeneas.Std.Array T1 N1) (_args : Aeneas.Std.Array T2 N2) :
    Aeneas.Std.Result fmt.Arguments :=
  Aeneas.Std.Result.ok ()

/-- `Formatter::write_str`. No-op stub returning Ok. -/
def fmt.Formatter.write_str (f : fmt.Formatter) (_s : Aeneas.Std.Slice Aeneas.Std.U8) :
    Aeneas.Std.Result ((result.Result Unit fmt.Error) × fmt.Formatter) :=
  Aeneas.Std.Result.ok (result.Result.Ok (), f)

/-- `Formatter::debug_struct_field1_finish`. No-op stub returning Ok. -/
def fmt.Formatter.debug_struct_field1_finish
    {T : Type} (f : fmt.Formatter)
    (_name : Aeneas.Std.Slice Aeneas.Std.U8)
    (_field : Aeneas.Std.Slice Aeneas.Std.U8)
    (_value : T) :
    Aeneas.Std.Result ((result.Result Unit fmt.Error) × fmt.Formatter) :=
  Aeneas.Std.Result.ok (result.Result.Ok (), f)

end core_models

end
