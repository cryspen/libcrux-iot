-- Axioms for constants that are missing from the current extraction.
import Aeneas
import CoreModels

open Aeneas Aeneas.Std Result

noncomputable section

-- libcrux_secrets::traits::Classify::Blanket::classify
-- Blanket impl that wraps any value into a successful Result.
namespace libcrux_secrets.traits.Classify.Blanket
axiom classify : {T : Type} → T → Aeneas.Std.Result T
end libcrux_secrets.traits.Classify.Blanket

namespace Aeneas.Std

-- Integer cast operations from libcrux_secrets
axiom U32.Insts.Libcrux_secretsIntCastOps.as_u64 : U32 → Result U64
axiom U64.Insts.Libcrux_secretsIntCastOps.as_u32 : U64 → Result U32

-- I32 range step instance (mirrors Usize.Insts.Core_modelsIterRangeStep)
axiom I32.Insts.Core_modelsIterRangeStep : core_models.iter.range.Step I32

-- Slice indexing via a SliceIndex instance
axiom Slice.Insts.Core_modelsOpsIndexIndex.index :
  {T I Output : Type} →
  core.slice.index.SliceIndex I (Slice T) Output →
  Slice T → I → Result Output

axiom Slice.Insts.Core_modelsOpsIndexIndexMut.index_mut :
  {T I Output : Type} →
  core.slice.index.SliceIndex I (Slice T) Output →
  Slice T → I → Result (Output × (Output → Slice T))

-- Array indexing via a SliceIndex instance
axiom Array.Insts.Core_modelsOpsIndexIndex.index :
  {T I Output : Type} → {N : Usize} →
  core.slice.index.SliceIndex I (Slice T) Output →
  Array T N → I → Result Output

axiom Array.Insts.Core_modelsOpsIndexIndexMut.index_mut :
  {T I Output : Type} → {N : Usize} →
  core.slice.index.SliceIndex I (Slice T) Output →
  Array T N → I → Result (Output × (Output → Array T N))

-- Display instance for Usize (used with fmt::rt::Argument::new_display)
axiom Usize.Insts.Core_modelsFmtDisplay : core_models.fmt.Display Usize

-- Debug instances
axiom Usize.Insts.Core_modelsFmtDebug : core_models.fmt.Debug Usize

-- Debug instance builder for Array (parameterised over element Debug)
axiom Array.Insts.Core_modelsFmtDebug :
  {T : Type} → (N : Usize) → core_models.fmt.Debug T → core_models.fmt.Debug (Array T N)

-- Slice index instance wrappers (identity coercions for the index/index_mut dispatch)
axiom Slice.Insts.Core_modelsOpsIndexIndex :
  {T I O : Type} → core.slice.index.SliceIndex I (Slice T) O → core.slice.index.SliceIndex I (Slice T) O

axiom Slice.Insts.Core_modelsOpsIndexIndexMut :
  {T I O : Type} → core.slice.index.SliceIndex I (Slice T) O → core.slice.index.SliceIndex I (Slice T) O

end Aeneas.Std

namespace core_models

-- core::result::Result::unwrap
axiom result.Result.unwrap :
  {T E : Type} → fmt.Debug E → result.Result T E → Aeneas.Std.Result T

-- core::fmt::Arguments::new
axiom fmt.Arguments.new :
  {N M : Aeneas.Std.Usize} →
  Aeneas.Std.Array Aeneas.Std.U8 N →
  Aeneas.Std.Array fmt.rt.Argument M →
  Aeneas.Std.Result fmt.Arguments

-- core::fmt::Formatter::write_str
axiom fmt.Formatter.write_str :
  fmt.Formatter → Aeneas.Std.Str →
  Aeneas.Std.Result (result.Result Unit fmt.Error × fmt.Formatter)

-- core::fmt::Formatter::debug_struct_field4_finish
axiom fmt.Formatter.debug_struct_field4_finish :
  fmt.Formatter → Aeneas.Std.Str →
  Aeneas.Std.Str → Aeneas.Std.Dyn (fun _dyn => fmt.Debug _dyn) →
  Aeneas.Std.Str → Aeneas.Std.Dyn (fun _dyn => fmt.Debug _dyn) →
  Aeneas.Std.Str → Aeneas.Std.Dyn (fun _dyn => fmt.Debug _dyn) →
  Aeneas.Std.Str → Aeneas.Std.Dyn (fun _dyn => fmt.Debug _dyn) →
  Aeneas.Std.Result (result.Result Unit fmt.Error × fmt.Formatter)

-- core::slice::[T]::copy_from_slice
axiom slice.Slice.copy_from_slice :
  {T : Type} → marker.Copy T →
  Aeneas.Std.Slice T → Aeneas.Std.Slice T → Aeneas.Std.Result (Aeneas.Std.Slice T)

-- Debug instance for shared references (&T modelled as T)
axiom Shared0T.Insts.Core_modelsFmtDebug :
  {T : Type} → fmt.Debug T → fmt.Debug T

-- Debug instance for array::TryFromSliceError
axiom array.TryFromSliceError.Insts.Core_modelsFmtDebug : fmt.Debug array.TryFromSliceError

-- SliceIndex instances for the core_models Range types
axiom ops.range.RangeUsize.Insts.Core_modelsSliceIndexSliceIndexSliceSlice :
  (T : Type) → Aeneas.Std.core.slice.index.SliceIndex
    (ops.range.Range Aeneas.Std.Usize) (Aeneas.Std.Slice T) (Aeneas.Std.Slice T)

axiom ops.range.RangeToUsize.Insts.Core_modelsSliceIndexSliceIndexSliceSlice :
  (T : Type) → Aeneas.Std.core.slice.index.SliceIndex
    (ops.range.RangeTo Aeneas.Std.Usize) (Aeneas.Std.Slice T) (Aeneas.Std.Slice T)

axiom ops.range.RangeFromUsize.Insts.Core_modelsSliceIndexSliceIndexSliceSlice :
  (T : Type) → Aeneas.Std.core.slice.index.SliceIndex
    (ops.range.RangeFrom Aeneas.Std.Usize) (Aeneas.Std.Slice T) (Aeneas.Std.Slice T)

end core_models

end -- noncomputable section
