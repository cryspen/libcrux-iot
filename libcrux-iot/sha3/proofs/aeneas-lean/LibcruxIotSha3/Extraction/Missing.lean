import Aeneas
import CoreModels
import HacspecSha3.Missing

open Aeneas Aeneas.Std Result

noncomputable section

namespace libcrux_secrets.traits.Classify.Blanket
def classify {T : Type} (a : T) : Aeneas.Std.Result T := ok a
end libcrux_secrets.traits.Classify.Blanket

namespace libcrux_secrets

def U32.Insts.Libcrux_secretsIntCastOps.as_u64 (x : U32) : Result U64 :=
  ok (UScalar.cast .U64 x)

def U64.Insts.Libcrux_secretsIntCastOps.as_u32 (x : U64) : Result U32 :=
  ok (UScalar.cast .U32 x)

end libcrux_secrets

namespace core_models

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

@[reducible] def Usize.Insts.Core_modelsFmtDisplay : core_models.fmt.Display Usize :=
  { fmt := fun _ f => ok (core_models.result.Result.Ok (), f) }

@[reducible] def Usize.Insts.Core_modelsFmtDebug : core_models.fmt.Debug Usize :=
  { dbg_fmt := fun _ f => ok (core_models.result.Result.Ok (), f) }

@[reducible] def Array.Insts.Core_modelsFmtDebug
  {T : Type} (_N : Usize) (_elem : core_models.fmt.Debug T) :
  core_models.fmt.Debug (Array T _N) :=
  { dbg_fmt := fun _ f => ok (core_models.result.Result.Ok (), f) }

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

def Shared0T.Insts.Core_modelsFmtDebug
  {T : Type} (d : fmt.Debug T) : fmt.Debug T := d

def cmRangeToUsizeToAeneas (r : ops.range.RangeTo Aeneas.Std.Usize) :
    Aeneas.Std.core.ops.range.RangeTo Aeneas.Std.Usize :=
  { «end» := r.«end» }

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
