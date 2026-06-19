import LibcruxIotMlDsa.Spec.Pure
import LibcruxIotMlDsa.Spec.Lift

/-!
# ML-DSA NTT FC campaign — target catalog (non-proving scaffold)

This is the `Plan.lean` of the SKILL §13 methodology: one entry per intended
`@[spec]` impl↔spec Triple, organized by phase, each with its **FC post** and a
3–5 line **proof sketch**. It is *scaffolding, not law* — when the actual mvcgen
residue diverges, adapt the post (§13.1).

* Campaign prompt:  `LibcruxIotMlDsa/CAMPAIGN_PROMPT.md`
* Ledger (MANDATORY, §13.12): `~/.claude/plans/iot-mldsa-campaign-ledger.md`
  — append one row per dispatch / REVIEWER pass / session boundary.
* Reference tree: `libcrux-iot/ml-kem/proofs/aeneas-lean/` (the completed
  analogue — mirror its `Spec/Lift`, `Ntt.lean`, `InvertNtt.lean`,
  `Polynomial/*Fc.lean`, `Matrix/*/FC.lean`).

Spec side is REAL (`Spec/Pure.lean`, `Spec/Parameters.lean`,
`Spec/Montgomery.lean`) and imported below. The impl-side Triples are written as
**commented skeletons** because they reference `Extraction/Funs.lean`, which is
generated in Phase 0 (the local hax/aeneas toolchain does not yet match the pin
— see `Extraction/Funs.lean`). Uncomment + fill each phase as `Funs.lean` lands.

Conventions (all phases): equality-form posts (§13.3); `@[spec high]`; one
`hax_mvcgen` per Triple; FC-from-day-one (§8.1); banned tactics (§9.1);
`#print axioms` clean; **STOP-and-report** on any provably-false seam; ⚠️ the
upstream-libcrux F* bounds are STRUCTURAL HINTS — re-derive the iot bounds with
`#eval`/`plausible`.
-/

namespace libcrux_iot_ml_dsa.Plan
open libcrux_iot_ml_dsa.Spec

-- Spec side compiles and is the FC-post target for every Triple below:
#check @Pure.ntt_pure
#check @Pure.intt_pure
#check @Pure.poly_pointwise_mul_pure
#check @Lift.liftZ

/-! ## Domain keystones (Phase 1, in `Spec/Montgomery.lean`)
`q=8380417`, `R=2³²`, `R⁻¹=8265825`, `q'=58728449`, `256⁻¹=8347681`,
`41978=R²·256⁻¹`, `ζ=1753`. Restate the load-bearing `#guard`s as `ZMod`
`theorem`s here when a proof needs them.
-/

/-! ## Phase 2 — L0 field-element FC (per `i32` lane, in `ZMod q`)

Targets (`simd/portable/arithmetic.rs`). Keystone: `montgomery_reduce_element`
= `value · R⁻¹ (mod q)`.

```
@[spec high] theorem montgomery_reduce_element_fc (value : Std.I64)
    (h : <bound on value, re-derived per §13.13>) :
  ⦃ ⌜ True ⌝ ⦄ arithmetic.montgomery_reduce_element value
  ⦃ ⇓ r => ⌜ Lift.liftZ_std r.val = (value.val : Zq) * (Montgomery.RINV : Zq)
            ∧ <output bound> ⌝ ⦄
-- sketch: unfold; the i64 → (hi,low,k,c) reduction equals value·R⁻¹ mod q by
--   q'·q ≡ 1 (mod R); discharge the i32 bound from h via scalar_tac.
```
Also: `montgomery_multiply_fe_by_fer` (= `x·y·R⁻¹`), `reduce_element` (Barrett
`(fe+2²²)>>23`, = identity mod q on canonical range), `add`, `subtract`.
-/

/-! ## Phase 3 — L1 per-SIMD-unit (`Coefficients`, 8 lanes) FC

8-lane fold over Phase 2: `montgomery_multiply`, `montgomery_multiply_by_constant`,
`add`, `subtract`, `reduce`. Post shape:
`lift_coeffs r = <per-lane Phase-2 op> (lift_coeffs input)` (per the 8 lanes).
-/

/-! ## Phase 4 — L2 butterfly FC + zeta bridge

Within-unit butterflies (`simd/portable/{ntt,invntt}.rs`):
`simd_unit_ntt_at_layer_{0,1,2}` (Cooley–Tukey, 4/2/1 zetas),
`simd_unit_invert_ntt_at_layer_{0,1,2}` (Gentleman–Sande); cross-unit
`outer_3_plus` (fwd + inv). Plus the **zeta bridge**:

```
theorem zeta_bridge (i : Nat) (hi : i < 256) :
  Lift.liftZ (<impl inline montgomery zeta at index i> : Int) = Parameters.zeta i
-- i.e. inline `zeta_r i ≡ ζ^BitRev8(i) · R (mod q)` ⇒ liftZ strips the R.
```
F* precedent: `unit_fe_post_lX` per-pair relations. Re-derive iot zeta indexing
from `Funs.lean` (the impl bakes zetas inline per layer fn).
-/

/-! ## Phase 5 — L3 NTT driver FC (the core results)

Forward (`ntt.rs::ntt`, `simd/portable/ntt.rs`):
```
@[spec high] theorem ntt_fc (re : <PolynomialRingElement>) (h : <input bound>) :
  ⦃ ⌜ True ⌝ ⦄ ntt.ntt re
  ⦃ ⇓ r => ⌜ Lift.lift_poly r = Pure.ntt_pure (Lift.lift_poly re) ⌝ ⦄
-- sketch: per-layer step-lemma + loop-driver compose (SKILL §13.6); layers 0–2
--   map within-unit butterflies over 32 units, layers 3–7 drive outer_3_plus;
--   compose 8 layers; zeta bridge (Phase 4) supplies the clean zetas.
```
Inverse (`ntt.rs::invert_ntt_montgomery`, `.../invntt.rs`):
```
@[spec high] theorem invert_ntt_montgomery_fc (re : <…>) (h : <input bound>) :
  ⦃ ⌜ True ⌝ ⦄ ntt.invert_ntt_montgomery re
  ⦃ ⇓ r => ⌜ Lift.lift_poly r = Pure.intt_pure (Lift.lift_poly re) ⌝ ⦄
-- sketch: 8 Gentleman–Sande layers then ×41978 finalize (= R²·256⁻¹), which
--   realizes the spec's reduce_polynomial (×256⁻¹) after R-reconciliation.
```
Per-layer drivers `ntt_at_layer_{0..7}_fc`, `invert_ntt_at_layer_{0..7}_fc` are
the §13.6 combinator lemmas the composers chain.
-/

/-! ## Phase 6 — pointwise multiply + poly reduce FC

`ntt.rs::ntt_multiply_montgomery` (pointwise) ↔ `Pure.poly_pointwise_mul_pure`
(with the per-seam `R`-factor); `ntt.rs::reduce` (Barrett over 256 lanes) ↔
identity mod q on bounded input.
-/

/-! ## Phase 7 — rounding / arithmetic FC (broadest scope)

`shift_left_then_reduce`, `power2round`, `decompose_element`, `compute_hint`
(`simd/portable/arithmetic.rs`); specs from
`~/libcrux-ml-dsa-proofs/specs/ml-dsa/src/arithmetic.rs`. These are NOT NTT but
in-scope per the chosen breadth; each needs its own `Spec/Pure`-side reference.
-/

/-! ## Phase 8 — matrix-level FC (broadest scope)

`matrix.rs::compute_as1_plus_s2`, `compute_matrix_x_mask` (Â∘ŝ + iNTT + add).
Requires the pinned `HacspecMlDsa` aeneas-lean extraction (see `lakefile.toml`),
composing the Phase-5/6 poly-level FCs. Post shape mirrors ML-KEM L7:
`hacspec_ml_dsa.matrix.<op> (lift … ) = .ok (lift … r)`.
Fallback if spec extraction is blocked: compose directly from `Spec/Pure`.
-/

end libcrux_iot_ml_dsa.Plan
