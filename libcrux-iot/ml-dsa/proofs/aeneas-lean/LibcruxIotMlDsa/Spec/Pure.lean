import LibcruxIotMlDsa.Spec.Parameters
import LibcruxIotMlDsa.Spec.Montgomery

/-!
# ML-DSA NTT — pure-Lean reference spec (clean Z_q)

Faithful translation of `~/libcrux-ml-dsa-proofs/specs/ml-dsa/src/ntt.rs`
(and `polynomial.rs::poly_pointwise_mul`). This is the analogue of ML-KEM's
`Spec/Pure.lean`: the FC campaign proves the libcrux-iot Montgomery-domain impl
equal (through the lift) to these functions.

The hacspec `mod_q` is the identity on `ZMod q`, so the spec ops are plain
`ZMod q` ring operations. Coefficients are indexed `[0,256)` via `Array … !`
(default-on-OOB) so no `Fin` bound proofs are needed.

⚠️ **Phase-1 draft.** These bodies are a careful by-hand translation but have
not been machine-checked against the compiler or `plausible` in this scaffold.
The first Phase-1 dispatch MUST:
  1. `lake build` this file, and
  2. `plausible`-check the spec-level round-trip `intt (ntt p) = p` and a small
     `#eval` cross-check vs the Rust spec, BEFORE any impl↔spec Triple relies on
     it. Fix the translation here if either fails (the spec is mutable; the impl
     is not).
-/

namespace libcrux_iot_ml_dsa.Spec.Pure
open libcrux_iot_ml_dsa.Spec.Parameters
open libcrux_iot_ml_dsa.Spec

/-- A spec polynomial: 256 coefficients in `Z_q` (length is a convention, kept
    by every constructor below). -/
abbrev SpecPoly := Array Zq

/-- Build a 256-element `SpecPoly` from an index function. -/
def build (f : Nat → Zq) : SpecPoly := ((List.range 256).map f).toArray

/-- Two `build`s agree if their index functions agree on `[0, 256)`. The driver
    FCs reduce a `lift_units r = ntt_layer (lift_units re) layer` post (both sides
    `build`s) to a per-index goal via this. -/
theorem build_congr {f g : Nat → Zq} (h : ∀ i, i < 256 → f i = g i) : build f = build g := by
  unfold build
  congr 1
  apply List.map_congr_left
  intro x hx
  rw [List.mem_range] at hx
  exact h x hx

/-- `(build f)[i]! = f i` for `i < 256`. Turns spec-side `(build …)[i]!`
    lookups (e.g. `(lift_units re)[i]!`) into the underlying index function. -/
theorem build_getElem (f : Nat → Zq) (i : Nat) (hi : i < 256) : (build f)[i]! = f i := by
  unfold build
  rw [getElem!_pos _ i (by simp; exact hi)]
  simp [List.getElem_map, List.getElem_range]

/-- `256⁻¹` as a field element (the `reduce_polynomial` scale). -/
def inv256 : Zq := (Montgomery.INV256 : Zq)

/-- One **forward** (Cooley–Tukey) NTT layer. `ntt.rs::ntt_layer`.
    `len = 2^layer`, base zeta index `k = 128/len`, per-block zeta
    `zeta (round + k)` with `round = i / (2·len)`. -/
def ntt_layer (p : SpecPoly) (layer : Nat) : SpecPoly :=
  let len := 1 <<< layer
  let k := 128 / len
  build (fun i =>
    let round := i / (2 * len)
    let idx := i % (2 * len)
    let z := zeta (round + k)
    if idx < len then p[i]! + z * p[i + len]!
    else p[i - len]! - z * p[i]!)

/-- **Forward NTT**: layers 7 → 0 (`ntt.rs::ntt`). -/
def ntt (p : SpecPoly) : SpecPoly :=
  [7, 6, 5, 4, 3, 2, 1, 0].foldl (fun acc layer => ntt_layer acc layer) p

/-- One **inverse** (Gentleman–Sande) NTT layer. `ntt.rs::intt_layer`.
    `len = 2^layer`, `k = 256/len − 1`, the odd half uses `−zeta (k − round)`. -/
def intt_layer (p : SpecPoly) (layer : Nat) : SpecPoly :=
  let len := 1 <<< layer
  let k := (256 / len) - 1
  build (fun i =>
    let round := i / (2 * len)
    let idx := i % (2 * len)
    if idx < len then p[i]! + p[i + len]!
    else (- zeta (k - round)) * (p[i - len]! - p[i]!))

/-- Final iNTT scale by `256⁻¹` (`ntt.rs::reduce_polynomial`). -/
def reduce_polynomial (p : SpecPoly) : SpecPoly := p.map (· * inv256)

/-- **Inverse NTT**: layers 0 → 7 then scale by `256⁻¹` (`ntt.rs::intt`). -/
def intt (p : SpecPoly) : SpecPoly :=
  reduce_polynomial
    ([0, 1, 2, 3, 4, 5, 6, 7].foldl (fun acc layer => intt_layer acc layer) p)

/-- Pointwise (NTT-domain) product (`polynomial.rs::poly_pointwise_mul`). -/
def poly_pointwise_mul (a b : SpecPoly) : SpecPoly :=
  build (fun i => a[i]! * b[i]!)

/-- Pointwise polynomial addition (`polynomial.rs::PolynomialRingElement::add`).
    The impl is a 32-unit loop calling per-lane `wrapping_add`; in clean `Z_q`
    this is lane-wise `+`. -/
def poly_add (a b : SpecPoly) : SpecPoly :=
  build (fun i => a[i]! + b[i]!)

/-- Pointwise polynomial subtraction
    (`polynomial.rs::PolynomialRingElement::subtract`). Lane-wise `-` in `Z_q`. -/
def poly_sub (a b : SpecPoly) : SpecPoly :=
  build (fun i => a[i]! - b[i]!)

/-- The all-zero spec polynomial (`polynomial.rs::PolynomialRingElement::zero`).
    The impl returns a 32-unit ring element whose every lane is `0`; lifting each
    lane (`liftZ 0 = 0`) gives this. -/
def zero_poly : SpecPoly := build (fun _ => 0)

/-! ## Canonical FC-post aliases (referenced by `Plan.lean`'s Triples). -/

/-- Forward-NTT reference for the FC posts. -/
abbrev ntt_pure : SpecPoly → SpecPoly := ntt

/-- Inverse-NTT reference for the FC posts. -/
abbrev intt_pure : SpecPoly → SpecPoly := intt

/-- Pointwise-multiply reference for the FC posts. -/
abbrev poly_pointwise_mul_pure : SpecPoly → SpecPoly → SpecPoly := poly_pointwise_mul

end libcrux_iot_ml_dsa.Spec.Pure
