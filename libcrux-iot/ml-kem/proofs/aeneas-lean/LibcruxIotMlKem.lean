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
