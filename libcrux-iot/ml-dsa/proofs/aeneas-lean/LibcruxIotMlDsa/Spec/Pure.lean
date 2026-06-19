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

/-! ## Canonical FC-post aliases (referenced by `Plan.lean`'s Triples). -/

/-- Forward-NTT reference for the FC posts. -/
abbrev ntt_pure : SpecPoly → SpecPoly := ntt

/-- Inverse-NTT reference for the FC posts. -/
abbrev intt_pure : SpecPoly → SpecPoly := intt

/-- Pointwise-multiply reference for the FC posts. -/
abbrev poly_pointwise_mul_pure : SpecPoly → SpecPoly → SpecPoly := poly_pointwise_mul

end libcrux_iot_ml_dsa.Spec.Pure
