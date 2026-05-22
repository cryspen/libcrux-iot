-- Phase 0(b) note: `import LibcruxIotMlKem.Extraction.Funs` currently
-- fails — Funs.lean references libcrux_secrets / core_models shims
-- that the pinned rust-core-models rev doesn't export. Re-add the
-- direct Funs import after Phase 0(b) lands (a hax re-extraction or
-- a Missing.lean stub set).
import LibcruxIotMlKem.Plan
