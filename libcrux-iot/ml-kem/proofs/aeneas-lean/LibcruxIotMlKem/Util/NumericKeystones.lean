/-
  # `Util.NumericKeystones` — Montgomery / NTT keystone identities

  Concrete `Nat`-arithmetic identities (`(_ * _) % q = _`) that anchor
  the ML-KEM Montgomery and inverse-NTT correctness arguments. Every
  identity here closes by plain `decide` over small Nat arithmetic and
  is referenced by name from the Triple-level proofs that need it.

  Conventions: `R = 2^16`, `q = 3329`. `R⁻¹ ≡ 169 (mod q)`.

  All proofs are `by decide` — never `native_decide` — so the kernel
  proof term is small and the file's `#print axioms` reports only the
  base `propext` / `Classical.choice` / `Quot.sound` triple (no
  `Lean.ofReduceBool` / `Lean.trustCompiler`).
-/

namespace libcrux_iot_ml_kem.Util

/-! ## Numeric keystones -/

/-- **B.1 `mont_R_inv_q`** — `R · 169 ≡ 1 (mod q)`. Used by every
    Layer 0/2/3/6 lemma that converts between Montgomery and standard
    domains (`montgomery_reduce_element_spec`, `montgomery_multiply_*`).
    The load-bearing identity behind L0.3. -/
theorem mont_R_inv_q : ((2^16 : Nat) * 169) % 3329 = 1 := by decide

/-- **B.2 `mont_1441_eq_inv128`** — `1441 · 128 ≡ R² (mod q)`. Combined
    with one Montgomery reduce (× R⁻¹), the net factor on the value
    after `montgomery_multiply(b, 1441)` is `R / 128 mod q`. This is
    exactly the "Montgomery-scale-by-1/128" used in `add_error_reduce`,
    `subtract_reduce`, etc. to absorb the deferred 1/N normalization
    of inverse NTT (L6.x). -/
theorem mont_1441_eq_inv128 :
    (1441 * 128) % 3329 = (2^16 * 2^16) % 3329 := by decide

/-- **B.3 `mont_2285_eq_R_mod_q`** — `2285 ≡ 2^16 (mod q)`. Used in
    `to_unsigned_field_modulus` to convert Montgomery-encoded → canonical
    representative before serialization (L5.x). -/
theorem mont_2285_eq_R_mod_q : 2285 = (2^16 : Nat) % 3329 := by decide

/-- **B.4 `mont_1353_eq_RR_mod_q`** — `1353 ≡ R² (mod q)`. The Rust
    function `to_standard_domain` is `montgomery_multiply(c, 1353)`;
    it lifts `x` to `R · x mod q` (since `x · R² · R⁻¹ = R · x`).
    Used by Layer 3 (NTT pre-domain) and Layer 6 (post-NTT lift). -/
theorem mont_1353_eq_RR_mod_q : 1353 = (2^16 * 2^16) % 3329 := by decide

/-! ## Additional keystones -/

/-- **`mont_qinv_R`** — `Q⁻¹_R · q ≡ 1 (mod R)`, the dual of
    `mont_R_inv_q`. With `Q⁻¹_R = 62209` (the precomputed Montgomery
    constant for `q = 3329, R = 2^16`) and `R = 2^16`, this is
    `(62209 · 3329) % 2^16 = 1`. The load-bearing identity for
    `montgomery_reduce_element_spec` (L0.3): it is what makes the
    integer formula `(value - k*q) / R` produce an exact integer
    rather than a quotient with leftover bits.

    Note: while `mont_R_inv_q` lives mod q (B.1), this lemma lives
    mod R — together they pin down both halves of the Montgomery
    reciprocal pair. -/
theorem mont_qinv_R : (62209 * 3329) % (2^16 : Nat) = 1 := by decide

/-- **`mont_128_169_512`** — INTT finalize keystone:
    `1441 · 169 ≡ 512 (mod q)`.

    Semantically this is "after multiplying by `1441` (= `R / 128 mod q`,
    B.2) and one Montgomery reduce (× R⁻¹ = 169, B.1), the leftover
    factor is `512 = 2^9 = R / 128`" — i.e. the deferred 1/128 from
    INTT comes out as the canonical small constant `512` in the
    standard domain. The literal `128` in the symbol name refers to
    the 1/128 normalization factor that this identity finalizes.

    Used by L6.4 (`subtract_reduce`) and the assembly bridges that
    funnel the post-INTT Montgomery state down to canonical
    representatives. -/
theorem mont_128_169_512 : (1441 * 169) % 3329 = 512 := by decide

end libcrux_iot_ml_kem.Util
