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

open Aeneas Aeneas.Std Result

noncomputable section

namespace libcrux_secrets.traits.Classify.Blanket
def classify {T : Type} (a : T) : Aeneas.Std.Result T := ok a
end libcrux_secrets.traits.Classify.Blanket

namespace Aeneas.Std

def I16.Insts.Libcrux_secretsIntCastOps.as_i32 (x : I16) : Result I32 :=
  ok (IScalar.cast .I32 x)

def I32.Insts.Libcrux_secretsIntCastOps.as_i16 (x : I32) : Result I16 :=
  ok (IScalar.cast .I16 x)

def U32.Insts.Libcrux_secretsIntCastOps.as_i32 (x : U32) : Result I32 :=
  ok (UScalar.hcast .I32 x)

end Aeneas.Std

namespace core_models

def num.I16.wrapping_neg (x : Std.I16) : Result Std.I16 :=
  rust_primitives.arithmetic.wrapping_sub_i16 (0#i16) x

end core_models

end
