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

-- `cmRangeToUsizeToAeneas` and `ops.range.RangeToUsize.Insts.Core_modelsSliceIndexSliceIndexSliceSlice`
-- moved to `HacspecSha3.Common` (factored out to share with LibcruxIotSha3).
-- The canonical (Sha3) variant returns `RangeTo Usize → RangeTo Usize` and
-- dispatches via `SliceIndexRangeToUsizeSlice.*` (RangeTo-faithful), rather
-- than the prior `RangeTo → Range start=0` form. Observationally equivalent
-- for `s[..end]` semantics.

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

-- `slice.Slice.split_at`, `slice.Slice.chunks_exact`, and
-- `slice.iter.ChunksExact.…SharedASlice.next` moved to
-- `HacspecSha3.Common` (factored to share with LibcruxIotMlKem).

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

-- `iter.range.StepI32` / `I32.Insts.Core_modelsIterRangeStep`,
-- `Usize.Insts.Core_modelsFmtDisplay`, and
-- `Shared0T.Insts.Core_modelsFmtDebug` moved to `HacspecSha3.Common`
-- (factored out to share with LibcruxIotSha3). The canonical
-- (Sha3) `I32.IterRangeStep` has real-behavior bodies for
-- `steps_between` / `forward_checked` / `backward_checked` (ml-kem
-- extraction does not iterate over I32 ranges, so the choice is
-- moot at use sites).

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

-- `array.Array.as_slice` moved to `HacspecSha3.Common` (factored).

-- `fmt.Arguments.new` and `fmt.Formatter.write_str` moved to
-- `HacspecSha3.Common`. The canonical `write_str` takes
-- `Aeneas.Std.Str` (matches the live LibcruxIotSha3 callers); the
-- prior MlKem variant took `Slice U8` but was dead code (no live
-- caller in HacspecMlKem extraction).

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
