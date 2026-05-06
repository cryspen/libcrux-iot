import Aeneas
import CoreModels

open Aeneas Aeneas.Std Result

noncomputable section

namespace libcrux_secrets.traits.Classify.Blanket
def classify {T : Type} (a : T) : Aeneas.Std.Result T := ok a
end libcrux_secrets.traits.Classify.Blanket

namespace Aeneas.Std

def U32.Insts.Libcrux_secretsIntCastOps.as_u64 (x : U32) : Result U64 :=
  ok (UScalar.cast .U64 x)

def U64.Insts.Libcrux_secretsIntCastOps.as_u32 (x : U64) : Result U32 :=
  ok (UScalar.cast .U32 x)

def I32.Insts.Core_modelsIterRangeStep : core_models.iter.range.Step I32 := {
  cloneInst       := { clone := fun x => Aeneas.Std.Result.ok x}
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

def Slice.Insts.Core_modelsOpsIndexIndex.index
  {T I Output : Type}
  (inst : core.slice.index.SliceIndex I (Slice T) Output)
  (s : Slice T) (i : I) : Result Output :=
  core.slice.index.Slice.index inst s i

def Slice.Insts.Core_modelsOpsIndexIndexMut.index_mut
  {T I Output : Type}
  (inst : core.slice.index.SliceIndex I (Slice T) Output)
  (s : Slice T) (i : I) : Result (Output × (Output → Slice T)) :=
  core.slice.index.Slice.index_mut inst s i

def Array.Insts.Core_modelsOpsIndexIndex.index
  {T I Output : Type} {N : Usize}
  (inst : core.slice.index.SliceIndex I (Slice T) Output)
  (arr : Array T N) (i : I) : Result Output :=
  core.slice.index.Slice.index inst (Array.to_slice arr) i

def Array.Insts.Core_modelsOpsIndexIndexMut.index_mut
  {T I Output : Type} {N : Usize}
  (inst : core.slice.index.SliceIndex I (Slice T) Output)
  (arr : Array T N) (i : I) : Result (Output × (Output → Array T N)) := do
  let (s, to_arr) := Array.to_slice_mut arr
  let (out, to_slice) ← core.slice.index.Slice.index_mut inst s i
  ok (out, fun o => to_arr (to_slice o))

@[reducible] def Usize.Insts.Core_modelsFmtDisplay : core_models.fmt.Display Usize :=
  { fmt := fun _ f => ok (core_models.result.Result.Ok (), f) }

@[reducible] def Usize.Insts.Core_modelsFmtDebug : core_models.fmt.Debug Usize :=
  { dbg_fmt := fun _ f => ok (core_models.result.Result.Ok (), f) }

@[reducible] def Array.Insts.Core_modelsFmtDebug
  {T : Type} (_N : Usize) (_elem : core_models.fmt.Debug T) :
  core_models.fmt.Debug (Array T _N) :=
  { dbg_fmt := fun _ f => ok (core_models.result.Result.Ok (), f) }

def Slice.Insts.Core_modelsOpsIndexIndex
  {T I O : Type} (inst : core.slice.index.SliceIndex I (Slice T) O) :
  core.slice.index.SliceIndex I (Slice T) O := inst

def Slice.Insts.Core_modelsOpsIndexIndexMut
  {T I O : Type} (inst : core.slice.index.SliceIndex I (Slice T) O) :
  core.slice.index.SliceIndex I (Slice T) O := inst

end Aeneas.Std

namespace core_models

def result.Result.unwrap
  {T E : Type} (_dbg : fmt.Debug E) (r : result.Result T E) :
  Aeneas.Std.Result T :=
  match r with
  | .Ok x => Aeneas.Std.Result.ok x
  | .Err _ => Aeneas.Std.Result.fail Aeneas.Std.Error.panic

def fmt.Arguments.new
  {N M : Aeneas.Std.Usize}
  (_ : Aeneas.Std.Array Aeneas.Std.U8 N)
  (_ : Aeneas.Std.Array fmt.rt.Argument M) :
  Aeneas.Std.Result fmt.Arguments :=
  Aeneas.Std.Result.ok ()

def fmt.Formatter.write_str
  (f : fmt.Formatter) (_ : Aeneas.Std.Str) :
  Aeneas.Std.Result (result.Result Unit fmt.Error × fmt.Formatter) :=
  Aeneas.Std.Result.ok (.Ok (), f)

def fmt.Formatter.debug_struct_field4_finish
  (f : fmt.Formatter) (_ : Aeneas.Std.Str)
  (_ : Aeneas.Std.Str) (_ : Aeneas.Std.Dyn (fun _dyn => fmt.Debug _dyn))
  (_ : Aeneas.Std.Str) (_ : Aeneas.Std.Dyn (fun _dyn => fmt.Debug _dyn))
  (_ : Aeneas.Std.Str) (_ : Aeneas.Std.Dyn (fun _dyn => fmt.Debug _dyn))
  (_ : Aeneas.Std.Str) (_ : Aeneas.Std.Dyn (fun _dyn => fmt.Debug _dyn)) :
  Aeneas.Std.Result (result.Result Unit fmt.Error × fmt.Formatter) :=
  Aeneas.Std.Result.ok (.Ok (), f)

def slice.Slice.copy_from_slice
  {T : Type} (_cpy : marker.Copy T)
  (dst : Aeneas.Std.Slice T) (src : Aeneas.Std.Slice T) :
  Aeneas.Std.Result (Aeneas.Std.Slice T) :=
  if Aeneas.Std.Slice.len dst = Aeneas.Std.Slice.len src then
    Aeneas.Std.Result.ok src
  else Aeneas.Std.Result.fail Aeneas.Std.Error.panic

def Shared0T.Insts.Core_modelsFmtDebug
  {T : Type} (d : fmt.Debug T) : fmt.Debug T := d

@[reducible] def array.TryFromSliceError.Insts.Core_modelsFmtDebug :
  fmt.Debug array.TryFromSliceError :=
  { dbg_fmt := fun _ f => Aeneas.Std.Result.ok (.Ok (), f) }

def cmRangeUsizeToAeneas (r : ops.range.Range Aeneas.Std.Usize) :
    Aeneas.Std.core.ops.range.Range Aeneas.Std.Usize :=
  { start := r.start, «end» := r.«end» }

def cmRangeToUsizeToAeneas (r : ops.range.RangeTo Aeneas.Std.Usize) :
    Aeneas.Std.core.ops.range.RangeTo Aeneas.Std.Usize :=
  { «end» := r.«end» }

@[reducible] def ops.range.RangeUsize.Insts.Core_modelsSliceIndexSliceIndexSliceSlice
  (T : Type) : Aeneas.Std.core.slice.index.SliceIndex
    (ops.range.Range Aeneas.Std.Usize) (Aeneas.Std.Slice T) (Aeneas.Std.Slice T) :=
  { sealedInst := {}
    get := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.get (cmRangeUsizeToAeneas r) s
    get_mut := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.get_mut (cmRangeUsizeToAeneas r) s
    get_unchecked := fun _ _ => Aeneas.Std.Result.fail Aeneas.Std.Error.undef
    get_unchecked_mut := fun _ _ => Aeneas.Std.Result.fail Aeneas.Std.Error.undef
    index := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.index (cmRangeUsizeToAeneas r) s
    index_mut := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.index_mut (cmRangeUsizeToAeneas r) s }

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

@[reducible] def ops.range.RangeFromUsize.Insts.Core_modelsSliceIndexSliceIndexSliceSlice
  (T : Type) : Aeneas.Std.core.slice.index.SliceIndex
    (ops.range.RangeFrom Aeneas.Std.Usize) (Aeneas.Std.Slice T) (Aeneas.Std.Slice T) :=
  let toFullRange (r : ops.range.RangeFrom Aeneas.Std.Usize) (s : Aeneas.Std.Slice T) :
      Aeneas.Std.core.ops.range.Range Aeneas.Std.Usize :=
    { start := r.start, «end» := Aeneas.Std.Slice.len s }
  { sealedInst := {}
    get := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.get (toFullRange r s) s
    get_mut := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.get_mut (toFullRange r s) s
    get_unchecked := fun _ _ => Aeneas.Std.Result.fail Aeneas.Std.Error.undef
    get_unchecked_mut := fun _ _ => Aeneas.Std.Result.fail Aeneas.Std.Error.undef
    index := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.index (toFullRange r s) s
    index_mut := fun r s =>
      Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.index_mut (toFullRange r s) s }

end core_models

end
