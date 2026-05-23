/-
  # `BitMlKem/SpecPure.lean` — Open Question I.7 resolution.

  The hacspec ML-KEM extraction (`HacspecMlKem.Extraction.Funs`) wraps
  every spec function in the Aeneas `Result` monad, even when the
  body is mathematically pure (no panic / divergence). The bit-side
  intermediate spec (`BitMlKem.Spec`) operates on `MontPoly =
  Vector (ZMod 3329) 256`, which is genuinely pure.

  Layer M.4 alg-equiv lemmas state equations of the form
    `bit_<op> (lift hacspec_input) = lift (Spec.<op>_pure hacspec_input)`
  where `Spec.<op>_pure` is the panic-stripped projection of the
  hacspec `Result`-monadic spec. This file defines those `_pure`
  aliases.

  Per arch plan §F.2 option (b): each alias is defined by pattern
  match on the `Result`. The companion *side lemmas* of the form
  `Spec.<op> args = .ok (Spec.<op>_pure args)` are panic-freedom
  obligations and can be discharged once panic-free is established
  for the `parameters.FieldElement.{add,sub,mul,neg}` primitives.

  ## Scope

  - Scalar `parameters.FieldElement.{add,sub,mul,neg}` get `_pure`
    aliases — they are used pointwise inside every `polynomial.*`
    closure in the hacspec extraction.
  - The three poly-level hacspec wrappers used by M.4 easy cluster
    (`polynomial.add_to_ring_element`, `polynomial.poly_barrett_reduce`,
    `polynomial.subtract_reduce`) get `_pure` aliases.

  ## Discipline

  - All `_pure` defs are `noncomputable` because the match-on-Result
    extraction does not reduce by `decide` for arbitrary inputs;
    callers reason about them via the side lemmas (TODO) or by
    direct `simp only [<op>_pure]` rewriting through M.4 proofs.
  - No Mathlib imports needed; this file lives above the M.1 barrier
    inheriting `ZMod 3329` transitively via `BitMlKem.Spec`.
-/
import LibcruxIotMlKem.BitMlKem.Spec

namespace libcrux_iot_ml_kem.BitMlKem.SpecPure

open Aeneas Aeneas.Std
open hacspec_ml_kem

/-! ## Default `FieldElement` (used as fall-through in `_pure` match). -/

/-- Canonical default for `parameters.FieldElement` — the zero element.
    Used as the fall-through branch in the `match` definitions below;
    chosen to be in canonical range so the lift through `zmodOfFE`
    gives `0 : ZMod 3329`. -/
def defaultFE : parameters.FieldElement := { val := (0#u16 : Std.U16) }

instance : Inhabited parameters.FieldElement := ⟨defaultFE⟩

/-! ## Scalar `_pure` aliases. -/

/-- Pure projection of `parameters.FieldElement.add`. The hacspec body
    computes `(self.val + other.val) % q` via U32 lifts, all of which
    are panic-free; this `_pure` extracts the `.ok` value. -/
noncomputable def FieldElement.add_pure
    (self other : parameters.FieldElement) : parameters.FieldElement :=
  match parameters.FieldElement.add self other with
  | .ok r => r
  | _ => defaultFE

/-- Pure projection of `parameters.FieldElement.sub`. Mirrors
    `add_pure`; hacspec body computes `(self.val + q - other.val) % q`. -/
noncomputable def FieldElement.sub_pure
    (self other : parameters.FieldElement) : parameters.FieldElement :=
  match parameters.FieldElement.sub self other with
  | .ok r => r
  | _ => defaultFE

/-- Pure projection of `parameters.FieldElement.mul`. -/
noncomputable def FieldElement.mul_pure
    (self other : parameters.FieldElement) : parameters.FieldElement :=
  match parameters.FieldElement.mul self other with
  | .ok r => r
  | _ => defaultFE

/-- Pure projection of `parameters.FieldElement.neg`. -/
noncomputable def FieldElement.neg_pure
    (self : parameters.FieldElement) : parameters.FieldElement :=
  match parameters.FieldElement.neg self with
  | .ok r => r
  | _ => defaultFE

/-! ## Poly-level `_pure` aliases.

    These wrap the 256-coefficient Aeneas-`Array` results into a pure
    `SpecPoly = Vector parameters.FieldElement 256` via per-lane
    extraction. The wrapper is panic-free at the M.4 caller level
    because `parameters.createi` itself is panic-free for the
    256-element shape. -/

/-- Pure projection of `polynomial.add_to_ring_element`. -/
noncomputable def polynomial.add_to_ring_element_pure
    (lhs rhs : Std.Array parameters.FieldElement 256#usize) :
    Std.Array parameters.FieldElement 256#usize :=
  match hacspec_ml_kem.polynomial.add_to_ring_element lhs rhs with
  | .ok r => r
  | _ => lhs

/-- Pure projection of `polynomial.poly_barrett_reduce`. -/
noncomputable def polynomial.poly_barrett_reduce_pure
    (p : Std.Array parameters.FieldElement 256#usize) :
    Std.Array parameters.FieldElement 256#usize :=
  match hacspec_ml_kem.polynomial.poly_barrett_reduce p with
  | .ok r => r
  | _ => p

/-- Pure projection of `polynomial.subtract_reduce`. -/
noncomputable def polynomial.subtract_reduce_pure
    (a b : Std.Array parameters.FieldElement 256#usize) :
    Std.Array parameters.FieldElement 256#usize :=
  match hacspec_ml_kem.polynomial.subtract_reduce a b with
  | .ok r => r
  | _ => a

/-! ## Side lemmas — panic-freedom (TODO, Phase 3.8).

    Each of the following lemmas should hold by a panic-freedom
    argument over the do-block of the hacspec function, structured
    as a chain of `simp [Spec.<op>]` + per-step `.ok`-discharge.
    Marked deferred — landing them is part of the M.4 NTT-cluster
    dispatch (where the panic-freedom chain is needed
    end-to-end through `ntt.butterfly`, `ntt.ntt_layer_n`, etc.).

    The shape:
    ```
    theorem FieldElement.add_eq_ok (a b : FE) :
        parameters.FieldElement.add a b = .ok (FieldElement.add_pure a b)
    ```
    See `iot-mlkem-campaign-continue.md` Watch-out: "decide closes
    once `parameters.FieldElement.add` panic-freedom is established".
-/

end libcrux_iot_ml_kem.BitMlKem.SpecPure
