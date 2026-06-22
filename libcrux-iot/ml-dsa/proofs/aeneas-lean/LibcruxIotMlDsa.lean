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

-- Phase-0: extraction + generic Util specs (ported from ml-kem).
import LibcruxIotMlDsa.Extraction.Funs
import LibcruxIotMlDsa.Util.SliceSpecs
import LibcruxIotMlDsa.Util.LoopSpecs
-- Phase-2: L0 scalar Montgomery reduction keystone (montgomery_reduce_element_spec).
import LibcruxIotMlDsa.Vector.Portable.Arithmetic
-- Phase-2: L1 elementwise loop infra + Coefficients add/subtract Triples.
import LibcruxIotMlDsa.Util.LoopHelper
import LibcruxIotMlDsa.Vector.Portable.Element
import LibcruxIotMlDsa.Vector.Portable.Ntt           -- L2 butterflies
import LibcruxIotMlDsa.Vector.Portable.InvNtt        -- L0 inverse butterflies
import LibcruxIotMlDsa.Vector.Portable.NttDriver     -- L3 forward NTT layer drivers
import LibcruxIotMlDsa.Vector.Portable.InvNttDriver  -- L2 inverse NTT within-unit driver
import LibcruxIotMlDsa.Vector.Portable.NttMaster     -- forward NTT master (8-layer compose)
import LibcruxIotMlDsa.Vector.Portable.InvNttMaster  -- inverse NTT master (8-layer + finalize)
import LibcruxIotMlDsa.Vector.Portable.Rounding      -- Phase-7 decompose dual-output keystone
import LibcruxIotMlDsa.Polynomial.Ntt                -- poly-layer NTT FCs (ntt / invert_ntt_montgomery)
import LibcruxIotMlDsa.Polynomial.Arithmetic         -- poly-layer add / subtract FCs
import LibcruxIotMlDsa.Polynomial.NttArith            -- poly-layer ntt_multiply_montgomery / reduce FCs
import LibcruxIotMlDsa.Polynomial.Convert             -- poly-layer zero / to_i32_array / from_i32_array FCs
-- Phases 3-8 (re-enable as the proof files land; ml-dsa has no `createi`):
-- import LibcruxIotMlDsa.Util.CreateI
-- import LibcruxIotMlDsa.Ntt                          -- L3 forward drivers
-- import LibcruxIotMlDsa.InvertNtt                    -- L3 inverse drivers
-- import LibcruxIotMlDsa.Polynomial.NttMultiply       -- L6 pointwise mul
-- import LibcruxIotMlDsa.Matrix.ComputeAs1PlusS2      -- L7 matrix
-- import LibcruxIotMlDsa.Matrix.ComputeMatrixXMask    -- L7 matrix
