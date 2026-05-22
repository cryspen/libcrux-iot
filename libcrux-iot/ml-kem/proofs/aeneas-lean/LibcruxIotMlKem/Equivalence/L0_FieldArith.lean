/-
  # `Equivalence/L0_FieldArith.lean` — Layer 0 field-arithmetic Triples

  The L0 layer's home. Contains `@[spec]` Triples for the leaf
  field-arithmetic primitives from `vector/portable/arithmetic.rs`:

  - **L0.3 `montgomery_reduce_element_spec`** — signed Montgomery
    reduction; **the inaugural proof-bearing Triple of the campaign**.
  - L0.1 `get_n_least_significant_bits_spec` (TODO)
  - L0.2 `barrett_reduce_element_spec` (TODO)
  - L0.4 `montgomery_multiply_fe_by_fer_spec` (TODO; trivial corollary of L0.3)

  See `Plan.lean` lines 686-860 for the per-Triple sketches and the
  upstream F* port references.
-/
import LibcruxIotMlKem.Plan
import LibcruxIotMlKem.Extraction.Funs
import LibcruxIotMlKem.Util.Montgomery

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_kem.Equivalence

open Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Util

/-! ## Local primitive helpers

    Two specs missing from upstream Aeneas Std at the pinned rev: a
    BV-level spec for `IScalar >>> UScalar` and the post-unfold value
    bridge for `IScalar.wrapping_mul`. Both are PR-ready upstream
    candidates (SKILL §Tier 2); kept local pending bump.
-/

/-- The Triple `⦃True⦄ x ⦃⇓ r => ⌜P r⌝⦄` closer for `x = .ok v`.
    Lifts a pure-Prop fact about the value into a Triple post. -/
private theorem triple_of_ok_l0 {α : Type} {x : Result α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, hp]

/-- BV-level spec for `IScalar.shiftRight_UScalar` — the
    arithmetic-shift-right operation on signed integers. The `bv`
    representation is `BitVec.sshiftRight`; on `Int` this is
    floor-division by `2^s.val` (matches `Int.shiftRight`). -/
theorem IScalar.shiftRight_UScalar_bv_eq
    {ty : Aeneas.Std.IScalarTy} {tys : Aeneas.Std.UScalarTy}
    (x : Aeneas.Std.IScalar ty) (s : Aeneas.Std.UScalar tys)
    (hs : s.val < ty.numBits) :
    Aeneas.Std.IScalar.shiftRight_UScalar x s = .ok ⟨x.bv.sshiftRight s.val⟩ := by
  simp only [Aeneas.Std.IScalar.shiftRight_UScalar, Aeneas.Std.IScalar.shiftRight]
  rw [if_pos hs]

/-! ## L0.3 — `montgomery_reduce_element_spec`

    Implements the upstream `Vector.Portable.Arithmetic.montgomery_reduce_element`
    correctness theorem. See `Plan.lean:773-819`.
-/

/-! ### Auxiliary `Int`-level Montgomery reduction (the L0.3 mathematical core)

    The Triple proof below threads the impl through `IScalar.cast` /
    `wrapping_mul` / `>>>` and discharges the resulting `Int`-equation
    via this single helper. Keeps the Triple body short. -/

/-- The closed integer formula that the impl computes for the
    Montgomery-reduced value, expressed in terms of the input `v`
    and the truncated multiplier `v16 := Int.bmod v (2^16)`.

    Used internally by the L0.3 Triple proof. The bound and the
    congruence are the two halves of the L0.3 postcondition. -/
private theorem mont_reduce_core
    (v : Int) (h_v : v.natAbs ≤ 2^16 * 3328) :
    let v16 := Int.bmod v (2^16)
    let k16 := Int.bmod (v16 * 62209) (2^16)
    let km  := k16 * 3329
    let res := v / (2^16 : Int) - km / (2^16 : Int)
    modq_eq (res * (2^16 : Int)) v 3329 ∧ res.natAbs ≤ 3328 + 1665 := by
  -- Standard bmod bounds for power-of-two:
  --   |bmod x (2^16)| ≤ 2^15, more precisely `-2^15 ≤ x ≤ 2^15 - 1`.
  have h_v16_lb : -(2^15 : Int) ≤ Int.bmod v (2^16) := by
    have := (Arith.Int.bmod_pow2_bounds 16 v).1; simpa using this
  have h_v16_ub : Int.bmod v (2^16) < (2^15 : Int) := by
    have := (Arith.Int.bmod_pow2_bounds 16 v).2; simpa using this
  have h_k16_lb : -(2^15 : Int) ≤ Int.bmod (Int.bmod v (2^16) * 62209) (2^16) := by
    have := (Arith.Int.bmod_pow2_bounds 16 (Int.bmod v (2^16) * 62209)).1
    simpa using this
  have h_k16_ub : Int.bmod (Int.bmod v (2^16) * 62209) (2^16) < (2^15 : Int) := by
    have := (Arith.Int.bmod_pow2_bounds 16 (Int.bmod v (2^16) * 62209)).2
    simpa using this
  -- |v| ≤ 3328 * 2^16
  have h_v_abs : -((2^16 : Int) * 3328) ≤ v ∧ v ≤ (2^16 : Int) * 3328 := by
    have h_nat : (v.natAbs : Int) ≤ ((2^16 * 3328 : Nat) : Int) := by exact_mod_cast h_v
    -- |v| = v.natAbs (as Int)
    have h_abs : |v| = (v.natAbs : Int) := Int.abs_eq_natAbs v
    have h_v_lt_abs : -|v| ≤ v ∧ v ≤ |v| := ⟨neg_abs_le v, le_abs_self v⟩
    refine ⟨?_, ?_⟩
    · have h1 : -(v.natAbs : Int) ≤ v := by rw [← h_abs]; exact h_v_lt_abs.1
      have h2 : ((2^16 * 3328 : Nat) : Int) = (2^16 : Int) * 3328 := by norm_cast
      omega
    · have h1 : v ≤ (v.natAbs : Int) := by rw [← h_abs]; exact h_v_lt_abs.2
      have h2 : ((2^16 * 3328 : Nat) : Int) = (2^16 : Int) * 3328 := by norm_cast
      omega
  set v16 := Int.bmod v (2^16)
  set k16 := Int.bmod (v16 * 62209) (2^16)
  set km := k16 * 3329
  -- Now derive (v - km) % 2^16 = 0:
  -- km = k16 * 3329; k16 ≡ v16 * 62209 (mod 2^16);
  -- so km ≡ v16 * 62209 * 3329 ≡ v16 (mod 2^16) (via 62209*3329 ≡ 1 mod 2^16).
  have h_km_mod : (v - km) % (2^16 : Int) = 0 := by
    -- km % R = k16 * 3329 % R = (v16 * 62209) * 3329 % R = v16 % R (via keystone).
    have h_keystone_int : (62209 * 3329 : Int) % (2^16) = 1 := by decide
    -- bmod_emod : Int.bmod x m % m = x % m
    have h_k16_emod : k16 % (2^16 : Int) = (v16 * 62209) % (2^16 : Int) := by
      change (Int.bmod (v16 * 62209) (2^16)) % (2^16 : Int) = (v16 * 62209) % (2^16 : Int)
      exact_mod_cast Int.bmod_emod
    have h_step1 : km % (2^16 : Int) = (v16 * (62209 * 3329)) % (2^16 : Int) := by
      change (k16 * 3329) % _ = _
      rw [Int.mul_emod, h_k16_emod, ← Int.mul_emod]
      congr 1; ring
    have h_step2 : km % (2^16 : Int) = v16 % (2^16 : Int) := by
      rw [h_step1, Int.mul_emod, h_keystone_int, mul_one, Int.emod_emod_of_dvd _ (dvd_refl _)]
    -- v % R = v16 % R via bmod_emod.
    have h_v_emod : v % (2^16 : Int) = v16 % (2^16 : Int) := by
      change v % (2^16 : Int) = (Int.bmod v (2^16)) % (2^16 : Int)
      exact_mod_cast Int.bmod_emod.symm
    rw [Int.sub_emod, h_v_emod, ← h_step2]; simp
  -- Apply Util.sub_div_of_emod_eq_zero
  have h_div_split : v / (2^16 : Int) - km / (2^16 : Int) = (v - km) / (2^16 : Int) := by
    exact libcrux_iot_ml_kem.Util.sub_div_of_emod_eq_zero v km (2^16) (by decide) h_km_mod
  refine ⟨?_, ?_⟩
  · -- modq_eq ((v/R - km/R) * R) v 3329, i.e. ((v/R - km/R) * R - v) % 3329 = 0.
    show ((v / (2^16 : Int) - km / (2^16 : Int)) * (2^16 : Int) - v) % 3329 = 0
    rw [h_div_split]
    -- Since R ∣ (v - km), (v - km)/R * R = v - km.
    have h_R_dvd : (2^16 : Int) ∣ (v - km) := Int.dvd_of_emod_eq_zero h_km_mod
    obtain ⟨q, hq⟩ := h_R_dvd
    have h_vm_div : (v - km) / (2^16 : Int) = q := by
      rw [hq]; exact Int.mul_ediv_cancel_left q (by decide)
    rw [h_vm_div]
    -- v - km = 2^16 * q, so q * 2^16 - v = -km = -(k16 * 3329).
    have h_q_eq : q * (2^16 : Int) - v = -km := by linarith [hq]
    rw [h_q_eq]
    show -(k16 * 3329) % 3329 = 0
    rw [show -(k16 * 3329) = (-k16) * 3329 by ring]
    exact Int.mul_emod_left _ _
  · -- res.natAbs ≤ 3328 + 1665.
    have h_v_div_bounds : -3328 ≤ v / (2^16 : Int) ∧ v / (2^16 : Int) ≤ 3328 := by
      obtain ⟨hl, hu⟩ := h_v_abs
      refine ⟨?_, ?_⟩
      · have h := Int.ediv_le_ediv (a := -((2^16 : Int) * 3328)) (b := v)
                    (c := (2^16 : Int)) (by decide) hl
        have h_const : (-(2^16 * 3328) : Int) / (2^16 : Int) = -3328 := by decide
        omega
      · have h := Int.ediv_le_ediv (a := v) (b := (2^16 : Int) * 3328)
                    (c := (2^16 : Int)) (by decide) hu
        have h_const : ((2^16 * 3328 : Int)) / (2^16 : Int) = 3328 := by decide
        omega
    have h_km_bounds : -(2^15 * 3329 : Int) ≤ km ∧ km ≤ ((2^15 - 1) * 3329 : Int) := by
      refine ⟨?_, ?_⟩
      · -- -(2^15) ≤ k16, so -(2^15) * 3329 ≤ k16 * 3329 = km
        have h := mul_le_mul_of_nonneg_right h_k16_lb (by decide : (0 : Int) ≤ 3329)
        have h_eq : (-(2^15 : Int)) * 3329 = -(2^15 * 3329) := by ring
        linarith [h, h_eq]
      · -- k16 ≤ 2^15 - 1, so km = k16 * 3329 ≤ (2^15 - 1) * 3329
        have h_k16_le : k16 ≤ 2^15 - 1 := by omega
        have h := mul_le_mul_of_nonneg_right h_k16_le (by decide : (0 : Int) ≤ 3329)
        exact h
    have h_km_div_bounds : -1665 ≤ km / (2^16 : Int) ∧ km / (2^16 : Int) ≤ 1664 := by
      obtain ⟨hl, hu⟩ := h_km_bounds
      refine ⟨?_, ?_⟩
      · have h := Int.ediv_le_ediv (a := -(2^15 * 3329 : Int)) (b := km)
                    (c := (2^16 : Int)) (by decide) hl
        have h_const : -(2^15 * 3329 : Int) / (2^16 : Int) = -1665 := by decide
        omega
      · have h := Int.ediv_le_ediv (a := km) (b := ((2^15 - 1) * 3329 : Int))
                    (c := (2^16 : Int)) (by decide) hu
        have h_const : (((2^15 - 1) * 3329 : Int)) / (2^16 : Int) = 1664 := by decide
        omega
    obtain ⟨h_vl, h_vu⟩ := h_v_div_bounds
    obtain ⟨h_kml, h_kmu⟩ := h_km_div_bounds
    have h_res_l : -(3328 + 1665 : Int) ≤ v / (2^16 : Int) - km / (2^16 : Int) := by linarith
    have h_res_u : v / (2^16 : Int) - km / (2^16 : Int) ≤ (3328 + 1665 : Int) := by linarith
    -- Bridge to natAbs via the |.|-natAbs identity.
    have h_abs_eq : (((v / (2^16 : Int) - km / (2^16 : Int)).natAbs : Int))
                    = |v / (2^16 : Int) - km / (2^16 : Int)| := by
      rw [Int.abs_eq_natAbs]
    have h_abs_le : |v / (2^16 : Int) - km / (2^16 : Int)| ≤ (3328 + 1665 : Int) := by
      rw [abs_le]; exact ⟨h_res_l, h_res_u⟩
    have h_int_le : ((v / (2^16 : Int) - km / (2^16 : Int)).natAbs : Int) ≤ (3328 + 1665 : Int) := by
      rw [h_abs_eq]; exact h_abs_le
    omega

/-- Closed-form value computed by the impl, as an `IScalar.I16`. -/
private def mont_reduce_impl_value (value : Std.I32) : Std.I16 :=
  let k := Aeneas.Std.I32.wrapping_mul
            (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32
              (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I16 value))
            (Aeneas.Std.UScalar.hcast Aeneas.Std.IScalarTy.I32
              (62209#u32))
  let km := Aeneas.Std.I32.wrapping_mul
              (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32
                (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I16 k))
              (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32
                (3329#i16))
  let i9 := (⟨km.bv.sshiftRight 16⟩ : Std.I32)
  let i11 := (⟨value.bv.sshiftRight 16⟩ : Std.I32)
  Aeneas.Std.I16.wrapping_sub
    (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I16 i11)
    (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I16 i9)

/-- The `do`-block reduces to `Result.ok (mont_reduce_impl_value value)`. -/
private theorem mont_reduce_element_eq_ok (value : Std.I32) :
    libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_reduce_element value
      = .ok (mont_reduce_impl_value value) := by
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_reduce_element
  unfold mont_reduce_impl_value
  -- Unfold the constants:
  have h_inv : libcrux_iot_ml_kem.vector.traits.INVERSE_OF_MODULUS_MOD_MONTGOMERY_R = 62209#u32 := by
    unfold libcrux_iot_ml_kem.vector.traits.INVERSE_OF_MODULUS_MOD_MONTGOMERY_R; rfl
  have h_q : libcrux_iot_ml_kem.vector.traits.FIELD_MODULUS = 3329#i16 := by
    unfold libcrux_iot_ml_kem.vector.traits.FIELD_MODULUS; rfl
  have h_shift : libcrux_iot_ml_kem.vector.portable.arithmetic.MONTGOMERY_SHIFT = 16#u8 := by
    unfold libcrux_iot_ml_kem.vector.portable.arithmetic.MONTGOMERY_SHIFT; rfl
  -- The shift amount as a U32, after cast, has val = 16 < 32.
  have h_shift_val : (Aeneas.Std.UScalar.cast Aeneas.Std.UScalarTy.U32 (16#u8 : U8)).val = 16 := by
    decide
  have h_shift_lt : (Aeneas.Std.UScalar.cast Aeneas.Std.UScalarTy.U32 (16#u8 : U8)).val
                      < Aeneas.Std.IScalarTy.I32.numBits := by
    rw [h_shift_val]; decide
  simp only [libcrux_secrets.traits.Classify.Blanket.classify,
             Aeneas.Std.I16.Insts.Libcrux_secretsIntCastOps.as_i32,
             Aeneas.Std.I32.Insts.Libcrux_secretsIntCastOps.as_i16,
             Aeneas.Std.U32.Insts.Libcrux_secretsIntCastOps.as_i32,
             Aeneas.Std.bind_tc_ok, Aeneas.Std.lift,
             core_models.num.I32.wrapping_mul,
             core_models.num.I16.wrapping_sub,
             rust_primitives.arithmetic.wrapping_mul_i32,
             rust_primitives.arithmetic.wrapping_sub_i16,
             h_inv, h_q, h_shift]
  -- After substitutions the goal should be a do-block of two `>>>` calls
  -- followed by `ok`; unfold the >>> instance + the shiftRight definition.
  simp only [HShiftRight.hShiftRight, Aeneas.Std.IScalar.shiftRight_UScalar,
             Aeneas.Std.IScalar.shiftRight, h_shift_val]
  rfl

/-! ### `.val` of the closed-form impl value, in `Int` terms.

    Used by the Triple proof to bridge BitVec/cast/shift to the
    `mont_reduce_core` helper. -/

private theorem mont_reduce_impl_value_val
    (value : Std.I32) (hb : value.val.natAbs ≤ 2^16 * 3328) :
    (mont_reduce_impl_value value).val
      = let v16 := Int.bmod value.val (2^16)
        let k16 := Int.bmod (v16 * 62209) (2^16)
        let km := k16 * 3329
        value.val / (2^16 : Int) - km / (2^16 : Int) := by
  unfold mont_reduce_impl_value
  -- |value.val| ≤ 3328 · 2^16, so all intermediate I32 operations fit (no wrap).
  set v : Int := value.val
  set v16 : Int := Int.bmod v (2^16)
  -- Bound v
  have h_v_abs_int : |v| ≤ (2^16 * 3328 : Int) := by
    rw [Int.abs_eq_natAbs]
    have : (v.natAbs : Int) ≤ ((2^16 * 3328 : Nat) : Int) := by exact_mod_cast hb
    have h2 : ((2^16 * 3328 : Nat) : Int) = (2^16 * 3328 : Int) := by norm_cast
    omega
  -- (cast .I16 value).val = bmod v (2^16) = v16
  have h_v16_eq : (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I16 value).val = v16 := by
    rw [Aeneas.Std.IScalar.cast_val_eq]; rfl
  -- v16 bounds
  have h_v16_bounds : -(2^15 : Int) ≤ v16 ∧ v16 < (2^15 : Int) := by
    refine ⟨?_, ?_⟩
    · have := (Arith.Int.bmod_pow2_bounds 16 v).1; simpa using this
    · have := (Arith.Int.bmod_pow2_bounds 16 v).2; simpa using this
  -- (cast .I32 (cast .I16 value)).val = v16 since |v16| < 2^15 < 2^31
  have h_v16_in_i32 : (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32
                        (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I16 value)).val = v16 := by
    have h_red : (Aeneas.Std.IScalarTy.I32.numBits - 1) = 31 := by decide
    have h_lb : -((2 : Int)^(Aeneas.Std.IScalarTy.I32.numBits - 1))
                ≤ (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I16 value).val := by
      rw [h_red, h_v16_eq]
      have h_v16_lb : -(2^15 : Int) ≤ v16 := h_v16_bounds.1
      have h_const : -((2 : Int)^31) ≤ -((2 : Int)^15) := by decide
      omega
    have h_ub : (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I16 value).val
                  < ((2 : Int)^(Aeneas.Std.IScalarTy.I32.numBits - 1)) := by
      rw [h_red, h_v16_eq]
      have h_v16_ub : v16 < (2^15 : Int) := h_v16_bounds.2
      have h_const : (2 : Int)^15 ≤ (2 : Int)^31 := by decide
      omega
    rw [Aeneas.Std.IScalar.val_mod_pow_inBounds _ _ h_lb h_ub]
    exact h_v16_eq
  -- (UScalar.hcast .I32 (62209#u32)).val = 62209
  have h_62209 : (Aeneas.Std.UScalar.hcast Aeneas.Std.IScalarTy.I32 (62209#u32 : U32)).val
                  = 62209 := by decide
  -- k = wrapping_mul (v16 as I32) (62209 as I32). |v16 * 62209| ≤ 2^15 * 62209 < 2^31.
  set k : Std.I32 := Aeneas.Std.I32.wrapping_mul
            (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32
              (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I16 value))
            (Aeneas.Std.UScalar.hcast Aeneas.Std.IScalarTy.I32 (62209#u32))
  -- k.val = v16 * 62209 (no wrap):
  -- Using BitVec.toInt_mul: (a*b).toInt = bmod (a.toInt * b.toInt) (2^32);
  -- |v16 * 62209| < 2^31 so the bmod is identity.
  have h_k_val : k.val = v16 * 62209 := by
    show (Aeneas.Std.I32.wrapping_mul _ _).val = _
    -- wrapping_mul_bv_eq : (wrapping_mul x y).bv = x.bv * y.bv
    have h_bv : k.bv = (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32
                        (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I16 value)).bv
                      * (Aeneas.Std.UScalar.hcast Aeneas.Std.IScalarTy.I32 (62209#u32)).bv := by
      show (Aeneas.Std.I32.wrapping_mul _ _).bv = _
      simp only [Aeneas.Std.I32.wrapping_mul, Aeneas.Std.IScalar.wrapping_mul]
    -- k.val = k.bv.toInt = bmod (a.bv.toInt * b.bv.toInt) (2^32);
    -- and a.bv.toInt = (cast .I32 ...).val = v16, b.bv.toInt = 62209.
    show k.bv.toInt = v16 * 62209
    rw [h_bv, BitVec.toInt_mul]
    -- IScalarTy.I32.numBits = 32, so bmod (v16 * 62209) (2^32).
    show Int.bmod _ _ = _
    have h_a_int : (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32
                    (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I16 value)).bv.toInt = v16 := by
      show (Aeneas.Std.IScalar.cast _ _).val = _
      exact h_v16_in_i32
    have h_b_int : (Aeneas.Std.UScalar.hcast Aeneas.Std.IScalarTy.I32 (62209#u32 : U32)).bv.toInt
                    = 62209 := by
      show (Aeneas.Std.UScalar.hcast _ _).val = _
      exact h_62209
    rw [h_a_int, h_b_int]
    -- bmod (v16 * 62209) (2^32) = v16 * 62209 since |v16 * 62209| < 2^31
    apply Arith.Int.bmod_pow2_eq_of_inBounds' 32 _ (by decide)
    · -- -(2^(32-1)) ≤ v16 * 62209
      have h_lb : (-(2^15 : Int)) * 62209 ≤ v16 * 62209 :=
        mul_le_mul_of_nonneg_right h_v16_bounds.1 (by decide : (0 : Int) ≤ 62209)
      have h_const : -((2 : Int)^(32-1)) ≤ -((2 : Int)^15) * 62209 := by decide
      omega
    · -- v16 * 62209 < 2^(32-1).
      have h_ub : v16 * 62209 < (2^15 : Int) * 62209 :=
        mul_lt_mul_of_pos_right h_v16_bounds.2 (by decide : (0 : Int) < 62209)
      have h_const : (2^15 : Int) * 62209 ≤ (2 : Int)^(32-1) := by decide
      omega
  -- Now (cast .I16 k).val = bmod k.val (2^16) = bmod (v16 * 62209) (2^16) = k16
  set k16 := Int.bmod (v16 * 62209) (2^16)
  have h_k16_eq : (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I16 k).val = k16 := by
    rw [Aeneas.Std.IScalar.cast_val_eq, h_k_val]; rfl
  have h_k16_bounds : -(2^15 : Int) ≤ k16 ∧ k16 < (2^15 : Int) := by
    refine ⟨?_, ?_⟩
    · have := (Arith.Int.bmod_pow2_bounds 16 (v16 * 62209)).1; simpa using this
    · have := (Arith.Int.bmod_pow2_bounds 16 (v16 * 62209)).2; simpa using this
  -- (cast .I32 (cast .I16 k)).val = k16
  have h_k16_in_i32 : (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32
                        (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I16 k)).val = k16 := by
    have h_red : (Aeneas.Std.IScalarTy.I32.numBits - 1) = 31 := by decide
    have h_lb : -((2 : Int)^(Aeneas.Std.IScalarTy.I32.numBits - 1))
                ≤ (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I16 k).val := by
      rw [h_red, h_k16_eq]
      have h_k16_lb : -(2^15 : Int) ≤ k16 := h_k16_bounds.1
      have h_const : -((2 : Int)^31) ≤ -((2 : Int)^15) := by decide
      omega
    have h_ub : (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I16 k).val
                  < ((2 : Int)^(Aeneas.Std.IScalarTy.I32.numBits - 1)) := by
      rw [h_red, h_k16_eq]
      have h_k16_ub : k16 < (2^15 : Int) := h_k16_bounds.2
      have h_const : (2 : Int)^15 ≤ (2 : Int)^31 := by decide
      omega
    rw [Aeneas.Std.IScalar.val_mod_pow_inBounds _ _ h_lb h_ub]
    exact h_k16_eq
  -- (cast .I32 (3329#i16)).val = 3329
  have h_3329 : (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 (3329#i16 : I16)).val
                 = 3329 := by decide
  -- km = wrapping_mul (k16 as I32) (3329 as I32). |k16 * 3329| < 2^15 * 3329 < 2^27 < 2^31.
  set km_aeneas : Std.I32 := Aeneas.Std.I32.wrapping_mul
              (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32
                (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I16 k))
              (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 (3329#i16))
  have h_km_val : km_aeneas.val = k16 * 3329 := by
    have h_bv : km_aeneas.bv = (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32
                        (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I16 k)).bv
                      * (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 (3329#i16)).bv := by
      show (Aeneas.Std.I32.wrapping_mul _ _).bv = _
      simp only [Aeneas.Std.I32.wrapping_mul, Aeneas.Std.IScalar.wrapping_mul]
    show km_aeneas.bv.toInt = _
    rw [h_bv, BitVec.toInt_mul]
    show Int.bmod _ _ = _
    rw [show (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32
              (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I16 k)).bv.toInt = k16 from h_k16_in_i32,
        show (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 (3329#i16 : I16)).bv.toInt = 3329
          from h_3329]
    apply Arith.Int.bmod_pow2_eq_of_inBounds' 32 _ (by decide)
    · have h_lb := mul_le_mul_of_nonneg_right h_k16_bounds.1 (by decide : (0 : Int) ≤ 3329)
      have h_const : -((2 : Int)^(32-1)) ≤ -((2 : Int)^15) * 3329 := by decide
      omega
    · have h_ub := mul_lt_mul_of_pos_right h_k16_bounds.2 (by decide : (0 : Int) < 3329)
      have h_const : (2^15 : Int) * 3329 ≤ (2 : Int)^(32-1) := by decide
      omega
  -- The two arithmetic shifts: i9 = km >> 16, i11 = value >> 16.
  -- |km.val| < 2^15 * 3329 < 2^27, so |i9.val| < 2^11 < 2^15 (fits in i16).
  -- |value.val| ≤ 3328 * 2^16, so |i11.val| ≤ 3328 < 2^15 (fits in i16).
  set i9 : Std.I32 := ⟨km_aeneas.bv.sshiftRight 16⟩
  set i11 : Std.I32 := ⟨value.bv.sshiftRight 16⟩
  -- i9.val = km.val / 2^16
  have h_i9_val : i9.val = km_aeneas.val / (2^16 : Int) := by
    show (km_aeneas.bv.sshiftRight 16).toInt = _
    rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
    norm_cast
  have h_i11_val : i11.val = value.val / (2^16 : Int) := by
    show (value.bv.sshiftRight 16).toInt = _
    rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
    norm_cast
  -- Bound i9 and i11 to fit in I16:
  -- i9.val = km.val / 2^16, |km.val| ≤ 2^15 * 3329, so |i9.val| ≤ 2^15 * 3329 / 2^16.
  have h_i9_bounds : -(2^15 : Int) ≤ i9.val ∧ i9.val < (2^15 : Int) := by
    rw [h_i9_val, h_km_val]
    have hl : -(2^15 * 3329 : Int) ≤ k16 * 3329 := by
      have h_lb := mul_le_mul_of_nonneg_right h_k16_bounds.1 (by decide : (0 : Int) ≤ 3329)
      have : (-(2^15 : Int)) * 3329 = -(2^15 * 3329 : Int) := by ring
      linarith
    have hu : k16 * 3329 ≤ ((2^15 - 1) * 3329 : Int) := by
      have h_le : k16 ≤ 2^15 - 1 := by omega
      exact mul_le_mul_of_nonneg_right h_le (by decide)
    refine ⟨?_, ?_⟩
    · have h := Int.ediv_le_ediv (a := -(2^15 * 3329 : Int)) (b := k16 * 3329)
                  (c := (2^16 : Int)) (by decide) hl
      have h_const : -(2^15 * 3329 : Int) / (2^16 : Int) = -1665 := by decide
      have : (-1665 : Int) ≥ -(2^15) := by decide
      omega
    · have h := Int.ediv_le_ediv (a := k16 * 3329) (b := ((2^15 - 1) * 3329 : Int))
                  (c := (2^16 : Int)) (by decide) hu
      have h_const : (((2^15 - 1) * 3329 : Int)) / (2^16 : Int) = 1664 := by decide
      have : (1664 : Int) < 2^15 := by decide
      omega
  have h_i11_bounds : -(2^15 : Int) ≤ i11.val ∧ i11.val < (2^15 : Int) := by
    rw [h_i11_val]
    have hl : -((2^16 : Int) * 3328) ≤ v := by
      have h_nat : (v.natAbs : Int) ≤ ((2^16 * 3328 : Nat) : Int) := by exact_mod_cast hb
      have h_abs : |v| = (v.natAbs : Int) := Int.abs_eq_natAbs v
      have h_v_lt_abs : -|v| ≤ v := neg_abs_le v
      have h2 : ((2^16 * 3328 : Nat) : Int) = (2^16 : Int) * 3328 := by norm_cast
      omega
    have hu : v ≤ (2^16 : Int) * 3328 := by
      have h_nat : (v.natAbs : Int) ≤ ((2^16 * 3328 : Nat) : Int) := by exact_mod_cast hb
      have h_abs : |v| = (v.natAbs : Int) := Int.abs_eq_natAbs v
      have h_v_lt_abs : v ≤ |v| := le_abs_self v
      have h2 : ((2^16 * 3328 : Nat) : Int) = (2^16 : Int) * 3328 := by norm_cast
      omega
    refine ⟨?_, ?_⟩
    · have h := Int.ediv_le_ediv (a := -((2^16 : Int) * 3328)) (b := v)
                  (c := (2^16 : Int)) (by decide) hl
      have h_const : (-((2^16 : Int) * 3328)) / (2^16 : Int) = -3328 := by decide
      have : (-3328 : Int) ≥ -(2^15) := by decide
      omega
    · have h := Int.ediv_le_ediv (a := v) (b := (2^16 : Int) * 3328)
                  (c := (2^16 : Int)) (by decide) hu
      have h_const : ((2^16 : Int) * 3328) / (2^16 : Int) = 3328 := by decide
      have : (3328 : Int) < 2^15 := by decide
      omega
  -- (cast .I16 i9).val = i9.val (since |i9.val| < 2^15)
  have h_c_val : (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I16 i9).val = i9.val := by
    have h_lb : -((2 : Int)^(Aeneas.Std.IScalarTy.I16.numBits - 1)) ≤ i9.val := by
      have h_red : (Aeneas.Std.IScalarTy.I16.numBits - 1) = 15 := by decide
      rw [h_red]; exact h_i9_bounds.1
    have h_ub : i9.val < ((2 : Int)^(Aeneas.Std.IScalarTy.I16.numBits - 1)) := by
      have h_red : (Aeneas.Std.IScalarTy.I16.numBits - 1) = 15 := by decide
      rw [h_red]; exact h_i9_bounds.2
    rw [Aeneas.Std.IScalar.val_mod_pow_inBounds _ _ h_lb h_ub]
  -- (cast .I16 i11).val = i11.val
  have h_vh_val : (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I16 i11).val = i11.val := by
    have h_lb : -((2 : Int)^(Aeneas.Std.IScalarTy.I16.numBits - 1)) ≤ i11.val := by
      have h_red : (Aeneas.Std.IScalarTy.I16.numBits - 1) = 15 := by decide
      rw [h_red]; exact h_i11_bounds.1
    have h_ub : i11.val < ((2 : Int)^(Aeneas.Std.IScalarTy.I16.numBits - 1)) := by
      have h_red : (Aeneas.Std.IScalarTy.I16.numBits - 1) = 15 := by decide
      rw [h_red]; exact h_i11_bounds.2
    rw [Aeneas.Std.IScalar.val_mod_pow_inBounds _ _ h_lb h_ub]
  -- Wrapping_sub on I16: result.val = bmod (vh.val - c.val) (2^16).
  -- We have |vh - c| ≤ 3328 + 1665 < 2^15, so no wrap.
  show (Aeneas.Std.I16.wrapping_sub _ _).val = _
  show (Aeneas.Std.I16.wrapping_sub
          (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I16 i11)
          (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I16 i9)).bv.toInt = _
  rw [show (Aeneas.Std.I16.wrapping_sub
              (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I16 i11)
              (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I16 i9)).bv
            = (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I16 i11).bv
              - (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I16 i9).bv from rfl,
      BitVec.toInt_sub]
  rw [show (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I16 i11).bv.toInt = i11.val
        from h_vh_val,
      show (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I16 i9).bv.toInt = i9.val
        from h_c_val]
  -- Goal: Int.bmod (i11.val - i9.val) (2^16) = v/R - km/R.
  -- Substitute h_i9_val, h_i11_val, h_km_val:
  rw [h_i11_val, h_i9_val, h_km_val]
  -- Need: bmod (v/R - k16*3329/R) (2^16) = v/R - k16*3329/R, i.e., the diff fits in [-2^15, 2^15).
  apply Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
  · -- -2^15 ≤ v/R - k16*3329/R: bounds give us [-4992, 4993], well within [-2^15, 2^15).
    -- We need |v/R - km/R| ≤ 3328 + 1665 = 4993 < 2^15 = 32768.
    have h_v_div : -3328 ≤ v / (2^16 : Int) ∧ v / (2^16 : Int) ≤ 3328 := by
      refine ⟨?_, ?_⟩
      · have := h_i11_bounds.1; rw [h_i11_val] at this
        have h_const : -3328 ≥ -(2^15 : Int) := by decide
        -- Stronger bound — re-derive directly.
        have hl : -((2^16 : Int) * 3328) ≤ v := by
          have h_nat : (v.natAbs : Int) ≤ ((2^16 * 3328 : Nat) : Int) := by exact_mod_cast hb
          have h_abs : |v| = (v.natAbs : Int) := Int.abs_eq_natAbs v
          have h_v_lt_abs : -|v| ≤ v := neg_abs_le v
          have h2 : ((2^16 * 3328 : Nat) : Int) = (2^16 : Int) * 3328 := by norm_cast
          omega
        have h := Int.ediv_le_ediv (a := -((2^16 : Int) * 3328)) (b := v)
                    (c := (2^16 : Int)) (by decide) hl
        have h_const2 : (-((2^16 : Int) * 3328)) / (2^16 : Int) = -3328 := by decide
        omega
      · have hu : v ≤ (2^16 : Int) * 3328 := by
          have h_nat : (v.natAbs : Int) ≤ ((2^16 * 3328 : Nat) : Int) := by exact_mod_cast hb
          have h_abs : |v| = (v.natAbs : Int) := Int.abs_eq_natAbs v
          have h_v_lt_abs : v ≤ |v| := le_abs_self v
          have h2 : ((2^16 * 3328 : Nat) : Int) = (2^16 : Int) * 3328 := by norm_cast
          omega
        have h := Int.ediv_le_ediv (a := v) (b := (2^16 : Int) * 3328)
                    (c := (2^16 : Int)) (by decide) hu
        have h_const : ((2^16 : Int) * 3328) / (2^16 : Int) = 3328 := by decide
        omega
    have h_km_div : -1665 ≤ k16 * 3329 / (2^16 : Int) ∧ k16 * 3329 / (2^16 : Int) ≤ 1664 := by
      refine ⟨?_, ?_⟩
      · have hl : -(2^15 * 3329 : Int) ≤ k16 * 3329 := by
          have h_lb := mul_le_mul_of_nonneg_right h_k16_bounds.1 (by decide : (0 : Int) ≤ 3329)
          have : (-(2^15 : Int)) * 3329 = -(2^15 * 3329 : Int) := by ring
          linarith
        have h := Int.ediv_le_ediv (a := -(2^15 * 3329 : Int)) (b := k16 * 3329)
                    (c := (2^16 : Int)) (by decide) hl
        have h_const : -(2^15 * 3329 : Int) / (2^16 : Int) = -1665 := by decide
        omega
      · have hu : k16 * 3329 ≤ ((2^15 - 1) * 3329 : Int) := by
          have h_le : k16 ≤ 2^15 - 1 := by omega
          exact mul_le_mul_of_nonneg_right h_le (by decide)
        have h := Int.ediv_le_ediv (a := k16 * 3329) (b := ((2^15 - 1) * 3329 : Int))
                    (c := (2^16 : Int)) (by decide) hu
        have h_const : (((2^15 - 1) * 3329 : Int)) / (2^16 : Int) = 1664 := by decide
        omega
    -- Goal: `-(2^(16-1)) ≤ ↑value / 2^16 - k16 * 3329 / 2^16`.
    -- Substitute `v = ↑value` so linarith can use h_v_div.
    show -((2 : Int)^(16-1)) ≤ v / 2^16 - k16 * 3329 / 2^16
    have h_2_15 : ((2 : Int)^(16-1)) = ((2 : Int)^15) := by decide
    rw [h_2_15]
    have h_15_le : (-(2^15) : Int) ≤ -4993 := by decide
    have hl1 : -3328 ≤ v / (2^16 : Int) := h_v_div.1
    have hl2 : k16 * 3329 / (2^16 : Int) ≤ 1664 := h_km_div.2
    linarith
  · have h_v_div : -3328 ≤ v / (2^16 : Int) ∧ v / (2^16 : Int) ≤ 3328 := by
      refine ⟨?_, ?_⟩
      · have hl : -((2^16 : Int) * 3328) ≤ v := by
          have h_nat : (v.natAbs : Int) ≤ ((2^16 * 3328 : Nat) : Int) := by exact_mod_cast hb
          have h_abs : |v| = (v.natAbs : Int) := Int.abs_eq_natAbs v
          have h_v_lt_abs : -|v| ≤ v := neg_abs_le v
          have h2 : ((2^16 * 3328 : Nat) : Int) = (2^16 : Int) * 3328 := by norm_cast
          omega
        have h := Int.ediv_le_ediv (a := -((2^16 : Int) * 3328)) (b := v)
                    (c := (2^16 : Int)) (by decide) hl
        have h_const : (-((2^16 : Int) * 3328)) / (2^16 : Int) = -3328 := by decide
        omega
      · have hu : v ≤ (2^16 : Int) * 3328 := by
          have h_nat : (v.natAbs : Int) ≤ ((2^16 * 3328 : Nat) : Int) := by exact_mod_cast hb
          have h_abs : |v| = (v.natAbs : Int) := Int.abs_eq_natAbs v
          have h_v_lt_abs : v ≤ |v| := le_abs_self v
          have h2 : ((2^16 * 3328 : Nat) : Int) = (2^16 : Int) * 3328 := by norm_cast
          omega
        have h := Int.ediv_le_ediv (a := v) (b := (2^16 : Int) * 3328)
                    (c := (2^16 : Int)) (by decide) hu
        have h_const : ((2^16 : Int) * 3328) / (2^16 : Int) = 3328 := by decide
        omega
    have h_km_div : -1665 ≤ k16 * 3329 / (2^16 : Int) ∧ k16 * 3329 / (2^16 : Int) ≤ 1664 := by
      refine ⟨?_, ?_⟩
      · have hl : -(2^15 * 3329 : Int) ≤ k16 * 3329 := by
          have h_lb := mul_le_mul_of_nonneg_right h_k16_bounds.1 (by decide : (0 : Int) ≤ 3329)
          have : (-(2^15 : Int)) * 3329 = -(2^15 * 3329 : Int) := by ring
          linarith
        have h := Int.ediv_le_ediv (a := -(2^15 * 3329 : Int)) (b := k16 * 3329)
                    (c := (2^16 : Int)) (by decide) hl
        have h_const : -(2^15 * 3329 : Int) / (2^16 : Int) = -1665 := by decide
        omega
      · have hu : k16 * 3329 ≤ ((2^15 - 1) * 3329 : Int) := by
          have h_le : k16 ≤ 2^15 - 1 := by omega
          exact mul_le_mul_of_nonneg_right h_le (by decide)
        have h := Int.ediv_le_ediv (a := k16 * 3329) (b := ((2^15 - 1) * 3329 : Int))
                    (c := (2^16 : Int)) (by decide) hu
        have h_const : (((2^15 - 1) * 3329 : Int)) / (2^16 : Int) = 1664 := by decide
        omega
    -- Goal: `↑value / 2^16 - k16 * 3329 / 2^16 < 2^(16-1)`.
    show v / 2^16 - k16 * 3329 / 2^16 < (2 : Int)^(16-1)
    have h_2_15 : ((2 : Int)^(16-1)) = ((2 : Int)^15) := by decide
    rw [h_2_15]
    have hu1 : v / (2^16 : Int) ≤ 3328 := h_v_div.2
    have hl2 : -1665 ≤ k16 * 3329 / (2^16 : Int) := h_km_div.1
    have : (3328 + 1665 : Int) < 2^15 := by decide
    linarith

@[spec]
theorem montgomery_reduce_element_spec
    (value : Std.I32) (hb : value.val.natAbs ≤ 2^16 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_reduce_element value
    ⦃ ⇓ r => ⌜ modq_eq (r.val * (2^16 : Int)) value.val 3329
              ∧ r.val.natAbs ≤ 3328 + 1665 ⌝ ⦄ := by
  apply triple_of_ok_l0 (v := mont_reduce_impl_value value)
    (mont_reduce_element_eq_ok value)
  rw [mont_reduce_impl_value_val value hb]
  exact mont_reduce_core value.val hb

end libcrux_iot_ml_kem.Equivalence
