-- Hand-written stubs for symbols missing in Aeneas / rust-core-models.
--
-- Phase-0 placeholder. The ML-DSA impl uses `libcrux_secrets::I32` coefficients,
-- so the generated `Funs.lean` will reference `libcrux_secrets.*` i32 cast +
-- classify/declassify functions. Port the exact set from
-- `ml-kem/.../Extraction/Missing.lean` (which is i16-centric) ADAPTED to i32,
-- adding/removing cast stubs to match the FIRST extraction's build errors —
-- do NOT copy the ml-kem list blind (different widths, different call sites).
--
-- The two blanket stubs below are width-agnostic and certainly needed.
import Aeneas
import CoreModels

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Result

noncomputable section

namespace libcrux_secrets.traits.Classify.Blanket
def classify {T : Type} (a : T) : Aeneas.Std.Result T := ok a
end libcrux_secrets.traits.Classify.Blanket

namespace libcrux_secrets.traits.Declassify.Blanket
def declassify {T : Type} (a : T) : Aeneas.Std.Result T := ok a
end libcrux_secrets.traits.Declassify.Blanket

-- TODO(Phase 0): add `libcrux_secrets.{I32,I64,U8,…}.Insts.Libcrux_secretsIntCastOps.as_*`
-- stubs in the `declassify → cast → classify` shape, per the first extraction.

end
