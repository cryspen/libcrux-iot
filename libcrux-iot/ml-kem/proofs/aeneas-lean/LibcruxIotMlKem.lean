-- Phase 0(b) (2026-05-22): Funs.lean is now in the import chain via
-- `LibcruxIotMlKem.Extraction.Missing` (see Missing.lean's header for
-- the five identifiers it stubs). The next plumbing step is Phase
-- 0(c) — author `hax_aeneas.py` so re-extraction preserves the
-- import patch (search marker: PHASE0B-MISSING-PATCH).
import LibcruxIotMlKem.Plan
import LibcruxIotMlKem.Extraction.Funs
import LibcruxIotMlKem.Util.SliceSpecs
import LibcruxIotMlKem.Util.LoopSpecs
import LibcruxIotMlKem.Util.CreateI
import LibcruxIotMlKem.Util.PortableVector
import LibcruxIotMlKem.Equivalence.L0_FieldArith
import LibcruxIotMlKem.Equivalence.L1_VectorElementOps
import LibcruxIotMlKem.Equivalence.L2_NTTSteps
import LibcruxIotMlKem.Equivalence.L3_NTTDrivers
import LibcruxIotMlKem.Equivalence.L6_PolyOps
import LibcruxIotMlKem.BitMlKem.Spec
import LibcruxIotMlKem.BitMlKem.Commute
import LibcruxIotMlKem.BitMlKem.StateIso
import LibcruxIotMlKem.BitMlKem.SpecPure
import LibcruxIotMlKem.BitMlKem.AlgEquiv
import LibcruxIotMlKem.BitMlKem.FCTargets
import LibcruxIotMlKem.BitMlKem.L7.Axioms
import LibcruxIotMlKem.BitMlKem.L7.Common
import LibcruxIotMlKem.BitMlKem.L7.Impl.ComputeMessage
import LibcruxIotMlKem.BitMlKem.L7.Correctness.ComputeMessage
import LibcruxIotMlKem.BitMlKem.L7.FC.ComputeMessage
import LibcruxIotMlKem.BitMlKem.L7.FC.ComputeVectorU
import LibcruxIotMlKem.BitMlKem.L7.FC.ComputeRingElementV
import LibcruxIotMlKem.Util.AutomationSandbox
