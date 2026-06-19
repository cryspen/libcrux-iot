-- ML-DSA NTT: impl ↔ spec equivalence (aeneas-lean).
-- See `LibcruxIotMlDsa/README.md` and the campaign scaffold
-- `LibcruxIotMlDsa/Plan.lean`.

-- Self-contained spec reference (clean Z_q) — builds without an extraction.
import LibcruxIotMlDsa.Spec.Parameters
import LibcruxIotMlDsa.Spec.Montgomery
import LibcruxIotMlDsa.Spec.Pure
import LibcruxIotMlDsa.Spec.Lift
-- Build-time spec validation (round-trip + Rust ZETAS cross-check, axiom-free).
import LibcruxIotMlDsa.Spec.Validation

-- Phase-0+ (re-enable once `hax_aeneas.py` has generated `Extraction/Funs.lean`
-- and `Util/` has been ported from ml-kem):
-- import LibcruxIotMlDsa.Extraction.Funs
-- import LibcruxIotMlDsa.Util.SliceSpecs
-- import LibcruxIotMlDsa.Util.LoopSpecs
-- import LibcruxIotMlDsa.Util.CreateI
-- import LibcruxIotMlDsa.Vector.Portable.Arithmetic   -- L0/L1
-- import LibcruxIotMlDsa.Vector.Portable.Ntt          -- L2 butterflies
-- import LibcruxIotMlDsa.Ntt                          -- L3 forward drivers
-- import LibcruxIotMlDsa.InvertNtt                    -- L3 inverse drivers
-- import LibcruxIotMlDsa.Polynomial.NttMultiply       -- L6 pointwise mul
-- import LibcruxIotMlDsa.Matrix.ComputeAs1PlusS2      -- L7 matrix
-- import LibcruxIotMlDsa.Matrix.ComputeMatrixXMask    -- L7 matrix
