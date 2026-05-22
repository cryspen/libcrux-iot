-- Phase 0(b) (2026-05-22): Funs.lean is now in the import chain via
-- `LibcruxIotMlKem.Extraction.Missing` (see Missing.lean's header for
-- the five identifiers it stubs). The next plumbing step is Phase
-- 0(c) — author `hax_aeneas.py` so re-extraction preserves the
-- import patch (search marker: PHASE0B-MISSING-PATCH).
import LibcruxIotMlKem.Plan
import LibcruxIotMlKem.Extraction.Funs
