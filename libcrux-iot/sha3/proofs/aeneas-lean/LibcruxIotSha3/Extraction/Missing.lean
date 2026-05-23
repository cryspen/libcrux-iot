import Aeneas
import CoreModels
import HacspecSha3.Missing
import LibcruxSecrets

open Aeneas Aeneas.Std Result

noncomputable section

-- `libcrux_secrets.{traits.Classify.Blanket.classify, U32.…as_u64,
-- U64.…as_u32}` used to be hand-stubbed here. The `LibcruxSecrets`
-- Lake dep (imported above) now provides the full
-- `libcrux_secrets.*` surface — every integer cast op + classify /
-- declassify Blankets — so the local stubs are redundant.

namespace core_models

-- `I32.Insts.Core_modelsIterRangeStep` and `Usize.Insts.Core_modelsFmtDisplay`
-- moved to `HacspecSha3.Common` (factored out to share with HacspecMlKem).

@[reducible] def Usize.Insts.Core_modelsFmtDebug : core_models.fmt.Debug Usize :=
  { dbg_fmt := fun _ f => ok (core_models.result.Result.Ok (), f) }

@[reducible] def Array.Insts.Core_modelsFmtDebug
  {T : Type} (_N : Usize) (_elem : core_models.fmt.Debug T) :
  core_models.fmt.Debug (Array T _N) :=
  { dbg_fmt := fun _ f => ok (core_models.result.Result.Ok (), f) }

-- `fmt.Arguments.new` and `fmt.Formatter.write_str` moved to
-- `HacspecSha3.Common`.

def fmt.Formatter.debug_struct_field4_finish
  (f : fmt.Formatter) (_ : Aeneas.Std.Str)
  (_ : Aeneas.Std.Str) (_ : Aeneas.Std.Dyn (fun _dyn => fmt.Debug _dyn))
  (_ : Aeneas.Std.Str) (_ : Aeneas.Std.Dyn (fun _dyn => fmt.Debug _dyn))
  (_ : Aeneas.Std.Str) (_ : Aeneas.Std.Dyn (fun _dyn => fmt.Debug _dyn))
  (_ : Aeneas.Std.Str) (_ : Aeneas.Std.Dyn (fun _dyn => fmt.Debug _dyn)) :
  Aeneas.Std.Result (result.Result Unit fmt.Error × fmt.Formatter) :=
  Aeneas.Std.Result.ok (.Ok (), f)

-- `Shared0T.Insts.Core_modelsFmtDebug`, `cmRangeToUsizeToAeneas`, and
-- `ops.range.RangeToUsize.Insts.Core_modelsSliceIndexSliceIndexSliceSlice`
-- moved to `HacspecSha3.Common` (factored out to share with HacspecMlKem).

end core_models

end
