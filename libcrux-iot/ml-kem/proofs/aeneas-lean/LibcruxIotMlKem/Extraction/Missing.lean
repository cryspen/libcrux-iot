-- Phase 0(b): hand-written stubs for symbols that the current
-- rust-core-models pin + hax/aeneas extraction leaves dangling in
-- `LibcruxIotMlKem/Extraction/Funs.lean`. Mirrors the SHA-3 sister
-- file `LibcruxIotSha3/Extraction/Missing.lean`.
--
-- Five identifiers needed (from `lake env lean Funs.lean` probe,
-- /tmp/mlkem-funs-S01-probe.log):
--   Aeneas.Std.I16.Insts.Libcrux_secretsIntCastOps.as_i32  (I16 → I32 sign-extend)
--   Aeneas.Std.I32.Insts.Libcrux_secretsIntCastOps.as_i16  (I32 → I16 truncate)
--   Aeneas.Std.U32.Insts.Libcrux_secretsIntCastOps.as_i32  (U32 → I32 zero-extend)
--   libcrux_secrets.traits.Classify.Blanket.classify       (polymorphic id → Result)
--   core_models.num.I16.wrapping_neg                       (I16 → I16 wrapping negation)
--
-- The first three are referenced unqualified in Funs.lean (e.g.
-- `I16.Insts.Libcrux_secretsIntCastOps.as_i32`) and resolve through
-- `open Aeneas.Std` to `Aeneas.Std.I16.…`, so we place them under
-- `namespace Aeneas.Std`. The latter two are referenced fully
-- qualified, so they go under their canonical namespaces.
--
-- `wrapping_neg` is not a primitive in rust-core-models, so we
-- express it via `rust_primitives.arithmetic.wrapping_sub_i16 0 x`,
-- mirroring how `core_models.num.I16.wrapping_sub` is defined in
-- `.lake/packages/rust-core-models/lean/CoreModels/Funs.lean:4564`.
import Aeneas
import CoreModels
import LibcruxSecrets
import HacspecSha3
import LibcruxIotSha3

open Aeneas Aeneas.Std Result

noncomputable section

-- The following five identifiers used to be hand-stubbed here:
--   libcrux_secrets.traits.Classify.Blanket.classify
--   libcrux_secrets.{I16,I32,U32}.Insts.Libcrux_secretsIntCastOps.as_*
-- They are now provided by the `LibcruxSecrets` Lake dep
-- (imported above), which directly extracts the libcrux-secrets crate
-- from `~/libcrux-ml-kem-proofs/crates/utils/secrets/`. Keeping them
-- here would cause "already declared" duplicate errors.
--
-- L0_FieldArith.lean's `simp only` lists still reference the old
-- `Aeneas.Std.I16.Insts.Libcrux_secretsIntCastOps.as_i32`-style
-- names. Those resolve through LibcruxSecrets's defs (the canonical
-- path is `libcrux_secrets.I16.Insts.…` but Aeneas.Std's I16 type
-- resolves to the same Std.I16, so the simp lemmas can be updated
-- if needed.

namespace core_models

def num.I16.wrapping_neg (x : Std.I16) : Result Std.I16 :=
  rust_primitives.arithmetic.wrapping_sub_i16 (0#i16) x

/-! ## Stubs ported from `specs/ml-kem`'s `HacspecMlKem/Missing.lean`.
    `LibcruxIotSha3.Missing` (transitively imported) covers
    `RangeToUsize` SliceIndex + `Usize.FmtDisplay/FmtDebug` +
    `I32.Insts.Core_modelsIterRangeStep`; we only add what's missing
    on top: iterator ops on ChunksExact + Array.as_slice. -/

-- `slice.Slice.split_at`, `slice.Slice.chunks_exact`,
-- `slice.iter.ChunksExact.…SharedASlice.next`, and
-- `array.Array.as_slice` moved to `HacspecSha3.Common` (factored
-- to share with HacspecMlKem).

/-- `Iterator` instance dict for `ChunksExact<T>` (item type: shared
    slice `&[T]`). Packages the `.next` stub from `HacspecSha3.Common`. -/
@[reducible] def slice.iter.ChunksExact.Insts.Core_modelsIterTraitsIteratorIteratorSharedASlice
    (T : Type) :
    iter.traits.iterator.Iterator (slice.iter.ChunksExact T) (Aeneas.Std.Slice T) :=
  { next := slice.iter.ChunksExact.Insts.Core_modelsIterTraitsIteratorIteratorSharedASlice.next }

/-- `Iterator::enumerate` for `ChunksExact<T>`. -/
def slice.iter.ChunksExact.Insts.Core_modelsIterTraitsIteratorIteratorSharedASlice.enumerate
    {T : Type} (it : slice.iter.ChunksExact T) :
    Aeneas.Std.Result (iter.adapters.enumerate.Enumerate (slice.iter.ChunksExact T)) :=
  Aeneas.Std.Result.ok { iter := it, count := 0#usize }

/-- `Iterator::enumerate` for `array::iter::IntoIter`. -/
def array.iter.IntoIter.Insts.Core_modelsIterTraitsIteratorIterator.enumerate
    {T : Type} {N : Aeneas.Std.Usize} (it : array.iter.IntoIter T N) :
    Aeneas.Std.Result (iter.adapters.enumerate.Enumerate (array.iter.IntoIter T N)) :=
  Aeneas.Std.Result.ok { iter := it, count := 0#usize }

end core_models

end
