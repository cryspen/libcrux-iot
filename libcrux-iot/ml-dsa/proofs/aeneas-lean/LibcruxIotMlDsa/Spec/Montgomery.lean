import LibcruxIotMlDsa.Spec.Parameters

/-!
# ML-DSA Montgomery keystones

The implementation works in the Montgomery domain with radix `R = 2³²`; the
clean spec (`Spec/Pure.lean`) does not. The equivalence proof therefore strips
`R` via the lift (`Spec/Lift.lean`) and reconciles per-seam `R`-factors.

All constants below are numerically verified (see the campaign plan's
`python3` check) and pinned here by elaboration-time `#guard` (no axioms). The
Phase-1 dispatch restates the load-bearing relations as `ZMod q` / `ZMod R`
`theorem`s for use inside proofs.
-/

namespace libcrux_iot_ml_dsa.Spec.Montgomery
open libcrux_iot_ml_dsa.Spec.Parameters

/-- Montgomery radix: the impl's `montgomery_reduce_element` shifts by 32. -/
abbrev R : Nat := 2 ^ 32

/-- `R mod q`. -/
abbrev RmodQ : Nat := 4193792

/-- `R⁻¹ mod q` — the logical effect of one `montgomery_reduce`
    (`mont_red value ≡ value · 8265825 (mod q)`). -/
abbrev RINV : Nat := 8265825

/-- `-q⁻¹ mod R` (`simd::traits::INVERSE_OF_MODULUS_MOD_MONTGOMERY_R`),
    used inside `montgomery_reduce_element`. -/
abbrev QPRIME : Nat := 58728449

/-- `256⁻¹ mod q` — the clean spec's `reduce_polynomial` scale. -/
abbrev INV256 : Nat := 8347681

/-- `R² · 256⁻¹ mod q` — the impl's `invert_ntt_montgomery` finalize constant
    (`montgomery_multiply_by_constant(·, 41978)`). -/
abbrev INTT_FINAL : Nat := 41978

#guard (R % Q) = RmodQ
#guard (R * RINV) % Q = 1                 -- R · R⁻¹ ≡ 1 (mod q)
#guard (QPRIME * Q) % R = 1               -- q' · q ≡ 1 (mod R)
#guard (256 * INV256) % Q = 1             -- 256 · 256⁻¹ ≡ 1 (mod q)
#guard (R * R * INV256) % Q = INTT_FINAL  -- 41978 = R²·256⁻¹ (mod q)
#guard (ZETA ^ 512) % Q = 1               -- ζ is a 512-th root of unity …
#guard (ZETA ^ 256) % Q = Q - 1           -- … and primitive (ζ²⁵⁶ = −1)

end libcrux_iot_ml_dsa.Spec.Montgomery
