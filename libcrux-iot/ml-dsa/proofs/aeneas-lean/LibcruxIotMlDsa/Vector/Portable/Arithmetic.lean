import LibcruxIotMlDsa.Extraction.Funs
import LibcruxIotMlDsa.Spec.Montgomery
import LibcruxIotMlDsa.Spec.Lift

/-!
  # `Vector/Portable/Arithmetic.lean` — Layer-0 scalar Montgomery reduction

  `@[spec high]` Triple for the leaf field-arithmetic primitive
  `simd.portable.arithmetic.montgomery_reduce_element`:

  - `get_n_least_significant_bits_eq_ok` — the mask-op closed form (U64 version)
  - `mont_reduce_element_eq_ok` — the do-block reduces to `.ok (mont_reduce_impl_value value)`
  - `mont_reduce_impl_value_val` — bridge to Int / bmod terms
  - `mont_reduce_core` — integer identity: `res·R = value - k·Q`
  - `montgomery_reduce_element_spec` — the final Triple (Phase-2 L0 keystone)
-/

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_dsa.Vector.Portable.Arithmetic
open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_dsa.Spec.Parameters
open libcrux_iot_ml_dsa.Spec.Montgomery
open libcrux_iot_ml_dsa.Spec.Lift

/-- The Triple `⦃True⦄ x ⦃⇓ r => ⌜P r⌝⦄` closer for `x = .ok v`. -/
private theorem triple_of_ok_l0 {α : Type} {x : Result α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply, hp]

/-! ## `get_n_least_significant_bits` (U64 version) -/

private theorem get_n_least_significant_bits_eq_ok
    (n : Std.U8) (value : Std.U64) (hn : n.val < 64) :
    libcrux_iot_ml_dsa.simd.portable.arithmetic.get_n_least_significant_bits n value
      = .ok ⟨value.bv &&& ((1#64 <<< n.val) - 1#64)⟩ := by
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.get_n_least_significant_bits
  have hn_lt : n.val < Aeneas.Std.UScalarTy.U64.numBits := hn
  simp only [HShiftLeft.hShiftLeft, Aeneas.Std.UScalar.shiftLeft_UScalar,
             Aeneas.Std.UScalar.shiftLeft, hn_lt, reduceIte,
             CoreModels.core.num.U64.wrapping_sub,
             rust_primitives.arithmetic.wrapping_sub_u64,
             Aeneas.Std.bind_tc_ok]
  rfl

/-! ## Closed-form value of the impl -/

def mont_reduce_impl_value (value : Std.I64) : Std.I32 :=
  let i    := Aeneas.Std.IScalar.hcast Aeneas.Std.UScalarTy.U64 value
  let i1   : Std.U64 := ⟨i.bv &&& ((1#64 <<< (32 : Nat)) - 1#64)⟩
  let t    : Std.U64 := ⟨i1.bv * (58728449#u64 : Std.U64).bv⟩
  let i2   : Std.U64 := ⟨t.bv &&& ((1#64 <<< (32 : Nat)) - 1#64)⟩
  let k    := Aeneas.Std.UScalar.hcast Aeneas.Std.IScalarTy.I32 i2
  let i3   := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I64 k
  let i4q  := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I64 (8380417#i32 : Std.I32)
  let km   := Aeneas.Std.I64.wrapping_mul i3 i4q
  let c    := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 (⟨km.bv.sshiftRight 32⟩ : Std.I64)
  let vh   := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 (⟨value.bv.sshiftRight 32⟩ : Std.I64)
  Aeneas.Std.I32.wrapping_sub vh c

theorem mont_reduce_element_eq_ok (value : Std.I64) :
    libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_reduce_element value
      = .ok (mont_reduce_impl_value value) := by
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_reduce_element mont_reduce_impl_value
  have h_inv : libcrux_iot_ml_dsa.simd.traits.INVERSE_OF_MODULUS_MOD_MONTGOMERY_R = 58728449#u64 := by
    unfold libcrux_iot_ml_dsa.simd.traits.INVERSE_OF_MODULUS_MOD_MONTGOMERY_R; rfl
  have h_q : libcrux_iot_ml_dsa.simd.traits.FIELD_MODULUS = 8380417#i32 := by
    unfold libcrux_iot_ml_dsa.simd.traits.FIELD_MODULUS; rfl
  have h_shift : libcrux_iot_ml_dsa.simd.portable.arithmetic.MONTGOMERY_SHIFT = 32#u8 := by
    unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.MONTGOMERY_SHIFT; rfl
  simp only [libcrux_secrets.traits.Classify.Blanket.classify,
             libcrux_secrets.traits.Declassify.Blanket.declassify,
             libcrux_secrets.I64.Insts.Libcrux_secretsIntCastOps.as_u64,
             libcrux_secrets.I64.Insts.Libcrux_secretsIntCastOps.as_i32,
             libcrux_secrets.U64.Insts.Libcrux_secretsIntCastOps.as_i32,
             libcrux_secrets.I32.Insts.Libcrux_secretsIntCastOps.as_i64,
             Aeneas.Std.bind_tc_ok, Aeneas.Std.lift,
             CoreModels.core.num.I64.wrapping_mul, CoreModels.core.num.I32.wrapping_sub,
             rust_primitives.arithmetic.wrapping_mul_i64, rust_primitives.arithmetic.wrapping_sub_i32,
             h_inv, h_q, h_shift]
  have h_glsb : ∀ (vv : Std.U64),
      libcrux_iot_ml_dsa.simd.portable.arithmetic.get_n_least_significant_bits 32#u8 vv
        = .ok ⟨vv.bv &&& ((1#64 <<< (32 : Nat)) - 1#64)⟩ :=
    fun vv => get_n_least_significant_bits_eq_ok 32#u8 vv (by decide)
  simp only [h_glsb, Aeneas.Std.bind_tc_ok]
  simp only [HShiftRight.hShiftRight, Aeneas.Std.IScalar.shiftRight_UScalar,
             Aeneas.Std.IScalar.shiftRight,
             show (32#u8 : U8).val < Aeneas.Std.IScalarTy.I64.numBits from by decide,
             reduceIte]
  rfl

/-! ## `.val` in Int terms -/

private theorem mont_reduce_impl_value_val
    (value : Std.I64) (hb : value.val.natAbs ≤ 2^55) :
    (mont_reduce_impl_value value).val
      = let v32 := Int.bmod value.val (2^32)
        let k32 := Int.bmod (v32 * 58728449) (2^32)
        let km  := k32 * 8380417
        value.val / (2^32 : Int) - km / (2^32 : Int) := by
  unfold mont_reduce_impl_value
  set v : Int := value.val
  have h_v_abs : |v| ≤ (2^55 : Int) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hb
  have h_v32_lb : -(2^31 : Int) ≤ Int.bmod v (2^32) := (Arith.Int.bmod_pow2_bounds 32 v).1
  have h_v32_ub : Int.bmod v (2^32) < (2^31 : Int) := (Arith.Int.bmod_pow2_bounds 32 v).2
  set v32 := Int.bmod v (2^32)
  set k32 := Int.bmod (v32 * 58728449) (2^32)
  have h_k32_lb : -(2^31 : Int) ≤ k32 := (Arith.Int.bmod_pow2_bounds 32 (v32 * 58728449)).1
  have h_k32_ub : k32 < (2^31 : Int) := (Arith.Int.bmod_pow2_bounds 32 (v32 * 58728449)).2

  -- i.bv = value.bv  (IScalar.hcast .U64 reinterprets same bits)
  have h_i_bv : (Aeneas.Std.IScalar.hcast Aeneas.Std.UScalarTy.U64 value).bv = value.bv := by
    simp only [Aeneas.Std.IScalar.hcast]
    change value.bv.signExtend 64 = value.bv
    exact BitVec.signExtend_eq value.bv

  -- Helper: (value.bv.toNat : Int) % 2^32 = v % 2^32
  have h_bv_val_emod : (value.bv.toNat : Int) % (2^32 : Int) = v % (2^32 : Int) := by
    have hval : v = value.bv.toInt := rfl
    rw [hval]
    simp only [BitVec.toInt_eq_toNat_cond]
    split_ifs <;> push_cast <;> omega

  -- mask.toNat = 2^32 - 1 (for 64-bit; avoid `decide` on large bitvec)
  have h_mask_toNat : ((1#64 <<< (32 : Nat)) - 1#64 : BitVec 64).toNat = 2^32 - 1 := by
    simp

  -- i1.val = v32 % 2^32 (as Nat)
  set i1 : Std.U64 := ⟨(Aeneas.Std.IScalar.hcast Aeneas.Std.UScalarTy.U64 value).bv
                        &&& ((1#64 <<< (32 : Nat)) - 1#64)⟩
  have h_i1_val : i1.val = (v32 % (2^32 : Int)).toNat := by
    change ((Aeneas.Std.IScalar.hcast Aeneas.Std.UScalarTy.U64 value).bv
            &&& ((1#64 <<< (32 : Nat)) - 1#64)).toNat = _
    rw [h_i_bv, BitVec.toNat_and, h_mask_toNat, Nat.and_two_pow_sub_one_eq_mod]
    -- Goal (Nat): value.bv.toNat % 2^32 = (v32 % 2^32 : Int).toNat
    have h_key : (value.bv.toNat : Int) % (2^32 : Int) = v32 % (2^32 : Int) := by
      rw [h_bv_val_emod]; exact Int.bmod_emod.symm
    have hnn : 0 ≤ v32 % (2^32 : Int) := Int.emod_nonneg _ (by decide)
    omega

  -- (i1.val : Int) = v32 % (2^32 : Int)
  have h_i1_val_int : (i1.val : Int) = v32 % (2^32 : Int) := by
    have h_nn : 0 ≤ v32 % (2^32 : Int) := Int.emod_nonneg _ (by decide)
    rw [h_i1_val, Int.toNat_of_nonneg h_nn]

  -- t.val = (i1.val * 58728449) % 2^64
  set t : Std.U64 := ⟨i1.bv * (58728449#u64 : Std.U64).bv⟩
  have h_t_val : t.val = (i1.val * 58728449) % 2^64 := by
    show (i1.bv * (58728449#u64).bv).toNat = _
    rw [BitVec.toNat_mul]; rfl

  -- i2.val = (i1.val * 58728449) % 2^32
  set i2 : Std.U64 := ⟨t.bv &&& ((1#64 <<< (32 : Nat)) - 1#64)⟩
  have h_i2_val : i2.val = (i1.val * 58728449) % 2^32 := by
    show (t.bv &&& ((1#64 <<< (32 : Nat)) - 1#64)).toNat = _
    rw [BitVec.toNat_and, h_mask_toNat, Nat.and_two_pow_sub_one_eq_mod]
    have : t.bv.toNat = (i1.val * 58728449) % 2^64 := h_t_val
    omega

  -- k.val = bmod (i2.val : Int) (2^32)
  set k := Aeneas.Std.UScalar.hcast Aeneas.Std.IScalarTy.I32 i2
  have h_k_val : k.val = Int.bmod (i2.val : Int) (2^32) := by
    show (i2.bv.zeroExtend 32).toInt = _
    rw [BitVec.toInt_setWidth]; rfl

  -- k.val = k32
  have h_k_eq_k32 : k.val = k32 := by
    rw [h_k_val, h_i2_val]
    -- Goal: Int.bmod (↑(↑i1 * 58728449 % 2^32)) (2^32) = k32
    have h_cast : ((i1.val * 58728449 % 2 ^ 32 : ℕ) : Int) = (i1.val : Int) * 58728449 % (2^32 : Int) := by
      omega
    rw [h_cast, h_i1_val_int]
    -- Goal: (v32 % 2^32 * 58728449 % 2^32).bmod (2^32) = k32.
    -- `Int.emod_bmod`/`Int.emod_mul_bmod` match the modulus only up to defeq ((2^32 : Int) vs
    -- ↑(2^32 : ℕ)); `rw` matches syntactically and fails here, so chain them in term mode.
    exact (Int.emod_bmod ((v32 % 2^32) * 58728449) (2^32)).trans (Int.emod_mul_bmod v32 (2^32))

  -- i3.val = k.val (sign-extend I32 → I64 preserves value)
  set i3 := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I64 k
  have h_i3_val : i3.val = k.val := by
    show (k.bv.signExtend 64).toInt = k.bv.toInt
    exact BitVec.toInt_signExtend_of_le (by decide)

  -- i4q.val = 8380417
  set i4q := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I64 (8380417#i32 : Std.I32)
  have h_i4q_val : i4q.val = 8380417 := by decide

  -- km.val = k.val * 8380417 (no wrap: |k| ≤ 2^31, |k * Q| ≤ 2^31 * Q < 2^63)
  set km := Aeneas.Std.I64.wrapping_mul i3 i4q
  have h_km_val : km.val = k.val * 8380417 := by
    show km.bv.toInt = _
    have h_bv : km.bv = i3.bv * i4q.bv := by
      show (Aeneas.Std.I64.wrapping_mul _ _).bv = _
      simp only [Aeneas.Std.I64.wrapping_mul_bv_eq]
    rw [h_bv, BitVec.toInt_mul]
    show Int.bmod _ _ = _
    rw [show i3.bv.toInt = k.val from h_i3_val, show i4q.bv.toInt = 8380417 from h_i4q_val,
        h_k_eq_k32]
    -- bmod (k32 * 8380417) (2^64) = k32 * 8380417 since |k32 * Q| ≤ 2^31 * Q < 2^63.
    -- Use bmod_pow2_eq_of_inBounds' 64 + norm_num bounds (NO omega on 2⁶³-scale: it trips
    -- the kernel recursion limit; mirrors the final 2^32 step below).
    apply Arith.Int.bmod_pow2_eq_of_inBounds' 64 _ (by decide)
    · -- -2^(64-1) ≤ k32 * 8380417
      have hlb := mul_le_mul_of_nonneg_right h_k32_lb (by norm_num : (0:Int) ≤ 8380417)
      refine le_trans ?_ hlb
      norm_num
    · -- k32 * 8380417 < 2^(64-1)
      have hub := mul_lt_mul_of_pos_right h_k32_ub (by norm_num : (0:Int) < 8380417)
      refine lt_of_lt_of_le hub ?_
      norm_num

  -- c.val = km.val / 2^32
  set c := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 (⟨km.bv.sshiftRight 32⟩ : Std.I64)
  have h_c_val : c.val = km.val / (2^32 : Int) := by
    have h_shr : (⟨km.bv.sshiftRight 32⟩ : Std.I64).val = km.val / (2^32 : Int) := by
      show (km.bv.sshiftRight 32).toInt = _
      rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]; norm_cast
    rw [Aeneas.Std.IScalar.val_mod_pow_inBounds]
    · exact h_shr
    · rw [h_shr, h_km_val, h_k_eq_k32]
      have h_lb := mul_le_mul_of_nonneg_right h_k32_lb (by decide : (0:Int) ≤ 8380417)
      have h_ediv := Int.ediv_le_ediv (c := 2^32) (by decide) h_lb
      have h_const : -(2^31 : Int) * 8380417 / 2^32 = -4190209 := by norm_num
      have h_pow31 : -(2:Int)^(IScalarTy.I32.numBits-1) = -2147483648 := by decide
      rw [h_const] at h_ediv; rw [h_pow31]; omega
    · rw [h_shr, h_km_val, h_k_eq_k32]
      -- bound k32 ≤ 2^31 via le_of_lt (avoids omega on raw 2^31 → kernel deep recursion);
      -- 2^31 * 8380417 / 2^32 = 8380417 / 2 = 4190208 (8380417 odd), same constant.
      have h_mul := mul_le_mul_of_nonneg_right (le_of_lt h_k32_ub) (by decide : (0:Int) ≤ 8380417)
      have h_ediv := Int.ediv_le_ediv (c := 2^32) (by decide) h_mul
      have h_const : (2^31 : Int) * 8380417 / 2^32 = 4190208 := by norm_num
      have h_pow31 : (2:Int)^(IScalarTy.I32.numBits-1) = 2147483648 := by decide
      rw [h_const] at h_ediv; rw [h_pow31]; omega

  -- vh.val = v / 2^32
  set vh := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 (⟨value.bv.sshiftRight 32⟩ : Std.I64)
  have h_vh_val : vh.val = v / (2^32 : Int) := by
    have h_shr : (⟨value.bv.sshiftRight 32⟩ : Std.I64).val = v / (2^32 : Int) := by
      show (value.bv.sshiftRight 32).toInt = _
      rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]; norm_cast
    rw [Aeneas.Std.IScalar.val_mod_pow_inBounds]
    · exact h_shr
    · rw [h_shr]
      have h_lb : -(2^55 : Int) ≤ v := le_trans (neg_le_neg h_v_abs) (neg_abs_le v)
      have h_ediv := Int.ediv_le_ediv (c := 2^32) (by decide) h_lb
      have h_const : -(2^55 : Int) / 2^32 = -8388608 := by norm_num
      have h_pow31 : -(2:Int)^(IScalarTy.I32.numBits-1) = -2147483648 := by decide
      rw [h_const] at h_ediv; rw [h_pow31]; omega
    · rw [h_shr]
      have h_ub : v ≤ (2^55 : Int) := le_trans (le_abs_self v) h_v_abs
      have h_ediv := Int.ediv_le_ediv (c := 2^32) (by decide) h_ub
      have h_const : (2^55 : Int) / 2^32 = 8388608 := by norm_num
      have h_pow31 : (2:Int)^(IScalarTy.I32.numBits-1) = 2147483648 := by decide
      rw [h_const] at h_ediv; rw [h_pow31]; omega

  -- Final: wrapping_sub vh c
  show (Aeneas.Std.I32.wrapping_sub vh c).bv.toInt = _
  rw [show (Aeneas.Std.I32.wrapping_sub vh c).bv = vh.bv - c.bv from rfl, BitVec.toInt_sub]
  rw [show vh.bv.toInt = vh.val from rfl, show c.bv.toInt = c.val from rfl]
  rw [h_vh_val, h_c_val, h_km_val, h_k_eq_k32]
  apply Arith.Int.bmod_pow2_eq_of_inBounds' 32 _ (by decide)
  · have h_v_div_lb : v / (2^32 : Int) ≥ -8388608 := by
      have h_lb : -(2^55 : Int) ≤ v := le_trans (neg_le_neg h_v_abs) (neg_abs_le v)
      have h_ediv := Int.ediv_le_ediv (c := 2^32) (by decide) h_lb
      have h_const : -(2^55 : Int) / 2^32 = -8388608 := by norm_num
      rw [h_const] at h_ediv; omega
    have h_km_div_ub : k32 * 8380417 / (2^32 : Int) ≤ 4190208 := by
      -- k32 ≤ 2^31 via le_of_lt (avoids omega on raw 2^31 → kernel deep recursion);
      -- 2^31 * 8380417 / 2^32 = 8380417 / 2 = 4190208 (8380417 odd), same constant.
      have h_mul := mul_le_mul_of_nonneg_right (le_of_lt h_k32_ub) (by decide : (0:Int) ≤ 8380417)
      have h_ediv := Int.ediv_le_ediv (c := 2^32) (by decide) h_mul
      have h_const : (2^31 : Int) * 8380417 / 2^32 = 4190208 := by norm_num
      rw [h_const] at h_ediv; omega
    have h31 : (2 : Int)^(32 - 1) = (2147483648 : Int) := by norm_num
    rw [h31]; omega
  · have h_v_div_ub : v / (2^32 : Int) ≤ 8388608 := by
      have h_ub : v ≤ (2^55 : Int) := le_trans (le_abs_self v) h_v_abs
      have h_ediv := Int.ediv_le_ediv (c := 2^32) (by decide) h_ub
      have h_const : (2^55 : Int) / 2^32 = 8388608 := by norm_num
      rw [h_const] at h_ediv; omega
    have h_km_div_lb : k32 * 8380417 / (2^32 : Int) ≥ -4190209 := by
      have h_mul := mul_le_mul_of_nonneg_right h_k32_lb (by decide : (0:Int) ≤ 8380417)
      have h_ediv := Int.ediv_le_ediv (c := 2^32) (by decide) h_mul
      have h_const : -(2^31 : Int) * 8380417 / 2^32 = -4190209 := by norm_num
      rw [h_const] at h_ediv; omega
    have h31 : (2 : Int)^(32 - 1) = (2147483648 : Int) := by norm_num
    rw [h31]; omega

/-! ## Integer core identity -/

private theorem mont_reduce_core
    (v : Int) (hb : v.natAbs ≤ 2^55) :
    let v32 := Int.bmod v (2^32)
    let k32 := Int.bmod (v32 * 58728449) (2^32)
    let km  := k32 * 8380417
    let res := v / (2^32 : Int) - km / (2^32 : Int)
    res * (2^32 : Int) = v - km := by
  set v32 := Int.bmod v (2^32)
  set k32 := Int.bmod (v32 * 58728449) (2^32)
  set km := k32 * 8380417
  -- (v - km) % 2^32 = 0
  have h_km_mod : (v - km) % (2^32 : Int) = 0 := by
    have h_keystone : (58728449 * 8380417 : Int) % (2^32) = 1 := by decide
    have h_k32_emod : k32 % (2^32 : Int) = (v32 * 58728449) % (2^32 : Int) :=
      Int.bmod_emod
    have h_km_emod : km % (2^32 : Int) = v32 % (2^32 : Int) := by
      change k32 * 8380417 % _ = _
      rw [Int.mul_emod, h_k32_emod, ← Int.mul_emod,
          show v32 * 58728449 * 8380417 = v32 * (58728449 * 8380417) by ring,
          Int.mul_emod, h_keystone, mul_one, Int.emod_emod_of_dvd _ (dvd_refl _)]
    rw [Int.sub_emod,
        show v % (2^32 : Int) = v32 % (2^32 : Int) from Int.bmod_emod.symm,
        ← h_km_emod]; simp
  have h_R_dvd : (2^32 : Int) ∣ (v - km) := Int.dvd_of_emod_eq_zero h_km_mod
  obtain ⟨q, hq⟩ := h_R_dvd
  have h_div_split : v / (2^32 : Int) - km / (2^32 : Int) = (v - km) / (2^32 : Int) :=
    sub_div_of_emod_eq_zero v km (2^32) (by decide) h_km_mod
  have h_vm_div : (v - km) / (2^32 : Int) = q := hq ▸ Int.mul_ediv_cancel_left q (by decide)
  show (v / (2^32 : Int) - km / (2^32 : Int)) * (2^32 : Int) = v - km
  rw [h_div_split, h_vm_div, hq]; ring

/-! ## L0 Triple -/

@[spec high]
theorem montgomery_reduce_element_spec (value : Std.I64) (hb : value.val.natAbs ≤ 2^55) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_reduce_element value
    ⦃ ⇓ r => ⌜ liftZ_std r.val = (value.val : Zq) * (RINV : Zq)
              ∧ r.val.natAbs ≤ 2^24 ⌝ ⦄ := by
  apply triple_of_ok_l0 (v := mont_reduce_impl_value value) (mont_reduce_element_eq_ok value)
  rw [mont_reduce_impl_value_val value hb]
  set v : Int := value.val
  set v32 := Int.bmod v (2^32)
  set k32 := Int.bmod (v32 * 58728449) (2^32)
  set km := k32 * 8380417
  set res := v / (2^32 : Int) - km / (2^32 : Int)
  have h_k32_lb : -(2^31 : Int) ≤ k32 := (Arith.Int.bmod_pow2_bounds 32 (v32 * 58728449)).1
  have h_k32_ub : k32 < (2^31 : Int) := (Arith.Int.bmod_pow2_bounds 32 (v32 * 58728449)).2
  have h_v_abs : |v| ≤ (2^55 : Int) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hb
  have h_res_R := mont_reduce_core v hb
  constructor
  · -- Equality clause: (res : Zq) = (v : Zq) * RINV
    show (res : Zq) = (v : Zq) * (RINV : Zq)
    exact mont_reduce_zmod v k32 res h_res_R
  · -- Bound: res.natAbs ≤ 2^24 (with |v| ≤ 2^55, |res| ≤ (2^55 + 2^31·q)/2^32 = 12578816 < 2^24)
    have h_km_abs : |km| ≤ (2^31 : Int) * 8380417 := by
      show |k32 * 8380417| ≤ _; rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_le.mpr ⟨h_k32_lb, le_of_lt h_k32_ub⟩) (by decide)
    have h_res_abs : |res| ≤ (2^24 : Int) := by
      have h_bound : |res| * (2^32 : Int) ≤ 2^55 + (2^31 : Int) * 8380417 := by
        calc |res| * (2^32 : Int)
            = |res * (2^32 : Int)| := by rw [abs_mul]; simp
          _ = |v - km| := by rw [h_res_R]
          _ ≤ |v| + |km| := abs_sub v km
          _ ≤ 2^55 + (2^31 : Int) * 8380417 := add_le_add h_v_abs h_km_abs
      have h_div_le := (Int.le_ediv_iff_mul_le (by decide : (0:Int) < 2^32)).mpr h_bound
      have h_const : (2^55 + (2^31 : Int) * 8380417) / 2^32 = 12578816 := by norm_num
      rw [h_const] at h_div_le
      exact le_trans h_div_le (by norm_num)
    rw [Int.abs_eq_natAbs] at h_res_abs; exact_mod_cast h_res_abs

/-! ## `reduce_element` — centered Barrett reduction (i32, q = 8380417, shift 23)

  The impl computes `fe - ((fe + 2^22) >> 23) * q`, a centered Barrett reduction:

      let i  := 1 <<< 22                     -- 2^22
      let i1 := wrapping_add fe i            -- fe + 2^22
      let q' := i1 >>> 23                     -- (fe + 2^22) / 2^23  (arithmetic shift)
      let i2 := wrapping_mul q' FIELD_MODULUS -- q' * q
      wrapping_sub fe i2                       -- fe - q' * q

  Derived precondition: `|fe| ≤ 2^31 - 2^23`. Binding constraint is the `wrapping_add`
  no-overflow (`fe + 2^22 ≤ 2^31 - 2^22 < 2^31`); this also yields `|quotient| ≤ 255`,
  so `|quotient * q| ≤ 255·q < 2^31` (the `wrapping_mul` no-overflow).

  Derived output bound: `|result| ≤ 6283009`, from the decomposition
  `result = (fe - q'·2^23) + q'·(2^23 - q) = (fe - q'·2^23) + q'·8191` where
  `|fe - q'·2^23| ≤ 2^22` (floor-div remainder) and `|q'·8191| ≤ 255·8191`,
  so `|result| ≤ 2^22 + 255·8191 = 6283009`. -/

/-- Closed-form value computed by the `reduce_element` impl, as an `IScalar.I32`.

    Stages the BV-level result of unfolding `reduce_element` so the Triple proof can
    apply `triple_of_ok_l0`. Mirrors ML-KEM's `barrett_reduce_impl_value`. -/
def reduce_impl_value (fe : Std.I32) : Std.I32 :=
  let i  : Std.I32 := ⟨(1#i32 : Std.I32).bv.shiftLeft 22⟩
  let i1 : Std.I32 := Aeneas.Std.I32.wrapping_add fe i
  let quotient : Std.I32 := ⟨i1.bv.sshiftRight 23⟩
  let i2 : Std.I32 := Aeneas.Std.I32.wrapping_mul quotient (8380417#i32)
  Aeneas.Std.I32.wrapping_sub fe i2

/-- The `do`-block reduces to `Result.ok (reduce_impl_value fe)`. -/
theorem reduce_element_eq_ok (fe : Std.I32) :
    libcrux_iot_ml_dsa.simd.portable.arithmetic.reduce_element fe
      = .ok (reduce_impl_value fe) := by
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.reduce_element reduce_impl_value
  have h_q : libcrux_iot_ml_dsa.simd.traits.FIELD_MODULUS = 8380417#i32 := by
    unfold libcrux_iot_ml_dsa.simd.traits.FIELD_MODULUS; rfl
  -- `1#i32 <<< 22#i32` is `IScalar.shiftLeft_IScalar`.
  have h_22_pos : (22#i32 : Std.I32).val ≥ 0 := by decide
  have h_22_lt : (22#i32 : Std.I32).toNat < Aeneas.Std.IScalarTy.I32.numBits := by decide
  -- `i1 >>> 23#i32` is `IScalar.shiftRight_IScalar`.
  have h_23_pos : (23#i32 : Std.I32).val ≥ 0 := by decide
  have h_23_lt : (23#i32 : Std.I32).toNat < Aeneas.Std.IScalarTy.I32.numBits := by decide
  simp only [HShiftLeft.hShiftLeft, Aeneas.Std.IScalar.shiftLeft_IScalar,
             Aeneas.Std.IScalar.shiftLeft,
             HShiftRight.hShiftRight, Aeneas.Std.IScalar.shiftRight_IScalar,
             Aeneas.Std.IScalar.shiftRight,
             h_22_pos, h_22_lt, h_23_pos, h_23_lt, reduceIte,
             CoreModels.core.num.I32.wrapping_add,
             CoreModels.core.num.I32.wrapping_mul,
             CoreModels.core.num.I32.wrapping_sub,
             rust_primitives.arithmetic.wrapping_add_i32,
             rust_primitives.arithmetic.wrapping_mul_i32,
             rust_primitives.arithmetic.wrapping_sub_i32,
             Aeneas.Std.bind_tc_ok, h_q]
  rfl

/-- Bridge: `(reduce_impl_value fe).val = fe.val - quotient * 8380417` (as `Int`), where
    `quotient = (fe.val + 2^22) / 2^23`, under `|fe.val| ≤ 2^31 - 2^23`. -/
private theorem reduce_impl_value_val
    (fe : Std.I32) (hb : fe.val.natAbs ≤ 2^31 - 2^23) :
    (reduce_impl_value fe).val
      = fe.val - ((fe.val + (2^22 : Int)) / (2^23 : Int)) * 8380417 := by
  unfold reduce_impl_value
  set v : Int := fe.val with hv_def
  -- |v| ≤ 2^31 - 2^23.
  have h_v_abs : |v| ≤ (2^31 - 2^23 : Int) := by
    rw [Int.abs_eq_natAbs]
    have : (v.natAbs : Int) ≤ ((2^31 - 2^23 : Nat) : Int) := by exact_mod_cast hb
    have h2 : ((2^31 - 2^23 : Nat) : Int) = (2^31 - 2^23 : Int) := by norm_num
    omega
  have h_v_lb : -(2^31 - 2^23 : Int) ≤ v := (abs_le.mp h_v_abs).1
  have h_v_ub : v ≤ (2^31 - 2^23 : Int) := (abs_le.mp h_v_abs).2
  -- i := 1 <<< 22 = 2^22.
  have h_i_val : (⟨(1#i32 : Std.I32).bv.shiftLeft 22⟩ : Std.I32).val = (2^22 : Int) := by decide
  set i : Std.I32 := ⟨(1#i32 : Std.I32).bv.shiftLeft 22⟩
  -- i1 := wrapping_add fe i. No wrap: -2^31 ≤ v + 2^22 < 2^31.
  set i1 : Std.I32 := Aeneas.Std.I32.wrapping_add fe i
  have h_sum_lb : -(2 : Int)^31 ≤ v + 2^22 := by
    have h_const : -(2 : Int)^31 ≤ -(2^31 - 2^23 : Int) + 2^22 := by norm_num
    omega
  have h_sum_ub : v + 2^22 < (2 : Int)^31 := by
    have h_const : (2^31 - 2^23 : Int) + 2^22 < (2 : Int)^31 := by norm_num
    omega
  have h_i1_val : i1.val = v + 2^22 := by
    show (Aeneas.Std.I32.wrapping_add _ _).val = _
    rw [Aeneas.Std.I32.wrapping_add_val_eq, h_i_val]
    apply Arith.Int.bmod_pow2_eq_of_inBounds' 32 _ (by decide)
    · have h_red : ((2 : Int)^(32-1)) = (2 : Int)^31 := by norm_num
      rw [h_red]; exact h_sum_lb
    · have h_red : ((2 : Int)^(32-1)) = (2 : Int)^31 := by norm_num
      rw [h_red]; exact h_sum_ub
  -- quotient := i1 >>> 23 = i1.val / 2^23.
  set quotient : Std.I32 := ⟨i1.bv.sshiftRight 23⟩
  have h_quotient_val : quotient.val = i1.val / (2^23 : Int) := by
    show (i1.bv.sshiftRight 23).toInt = _
    rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
    have h_pow_nat : ((2^23 : Nat) : Int) = ((2 : Int)^23) := by push_cast
    rw [h_pow_nat]
    show i1.bv.toInt / _ = i1.val / _
    rfl
  -- quotient = (v + 2^22) / 2^23.
  have h_quotient_eq : quotient.val = (v + 2^22) / (2^23 : Int) := by
    rw [h_quotient_val, h_i1_val]
  -- |quotient| ≤ 255 (so the multiply fits): -255 ≤ quotient ≤ 255.
  have h_quotient_bounds : -255 ≤ quotient.val ∧ quotient.val ≤ 255 := by
    rw [h_quotient_eq]
    refine ⟨?_, ?_⟩
    · have h_lb2 : -(2^31 - 2^23 : Int) + 2^22 ≤ v + 2^22 := by omega
      have h := Int.ediv_le_ediv (a := -(2^31 - 2^23 : Int) + 2^22)
                  (b := v + 2^22) (c := (2^23 : Int)) (by norm_num) h_lb2
      have h_const : (-(2^31 - 2^23 : Int) + 2^22) / (2^23 : Int) = -255 := by norm_num
      rw [h_const] at h; omega
    · have h_ub2 : v + 2^22 ≤ (2^31 - 2^23 : Int) + 2^22 := by omega
      have h := Int.ediv_le_ediv (a := v + 2^22)
                  (b := (2^31 - 2^23 : Int) + 2^22) (c := (2^23 : Int)) (by norm_num) h_ub2
      have h_const : ((2^31 - 2^23 : Int) + 2^22) / (2^23 : Int) = 255 := by norm_num
      rw [h_const] at h; omega
  -- i2 := wrapping_mul quotient 8380417. No wrap: |quotient * q| ≤ 255 * q < 2^31.
  have h_q_lit : (8380417#i32 : Std.I32).val = 8380417 := by decide
  set i2 : Std.I32 := Aeneas.Std.I32.wrapping_mul quotient (8380417#i32)
  have h_i2_val : i2.val = quotient.val * 8380417 := by
    show (Aeneas.Std.I32.wrapping_mul _ _).val = _
    rw [Aeneas.Std.I32.wrapping_mul_val_eq, h_q_lit]
    apply Arith.Int.bmod_pow2_eq_of_inBounds' 32 _ (by decide)
    · have h_lb := mul_le_mul_of_nonneg_right h_quotient_bounds.1 (by decide : (0 : Int) ≤ 8380417)
      have h_red : ((2 : Int)^(32-1)) = (2 : Int)^31 := by norm_num
      have h_const : -(2 : Int)^31 ≤ (-255 : Int) * 8380417 := by norm_num
      rw [h_red]; omega
    · have h_ub := mul_le_mul_of_nonneg_right h_quotient_bounds.2 (by decide : (0 : Int) ≤ 8380417)
      have h_red : ((2 : Int)^(32-1)) = (2 : Int)^31 := by norm_num
      have h_const : (255 : Int) * 8380417 < (2 : Int)^31 := by norm_num
      rw [h_red]; omega
  -- Bound on i2.val for the final wrapping_sub: |i2.val| ≤ 255 * 8380417.
  have h_i2_bounds : -(255 * 8380417 : Int) ≤ i2.val ∧ i2.val ≤ (255 * 8380417 : Int) := by
    rw [h_i2_val]
    constructor
    · have h_lb := mul_le_mul_of_nonneg_right h_quotient_bounds.1 (by decide : (0 : Int) ≤ 8380417)
      have : (-255 : Int) * 8380417 = -(255 * 8380417 : Int) := by ring
      omega
    · exact mul_le_mul_of_nonneg_right h_quotient_bounds.2 (by decide : (0 : Int) ≤ 8380417)
  -- result := wrapping_sub fe i2. No wrap: |v - i2.val| < 2^31.
  -- (|v| ≤ 2^31 - 2^23 and |i2| ≤ 255*q < 2^31; their difference still fits.)
  -- Concrete-numeral bounds on v (for the omega-on-difference steps).
  have h_vlb_lit : (-2139095040 : Int) ≤ v := by
    have h_const : -(2^31 - 2^23 : Int) = -2139095040 := by norm_num
    rw [h_const] at h_v_lb; exact h_v_lb
  have h_vub_lit : v ≤ (2139095040 : Int) := by
    have h_const : (2^31 - 2^23 : Int) = 2139095040 := by norm_num
    rw [h_const] at h_v_ub; exact h_v_ub
  have h_q255 : (255 * 8380417 : Int) = 2137006335 := by norm_num
  have h_sub_lb : -(2 : Int)^31 ≤ v - i2.val := by
    have h_i2_ub := h_i2_bounds.2
    have h_pow31 : (2 : Int)^31 = 2147483648 := by norm_num
    rw [h_q255] at h_i2_ub; rw [h_pow31]; omega
  have h_sub_ub : v - i2.val < (2 : Int)^31 := by
    have h_i2_lb := h_i2_bounds.1
    have h_pow31 : (2 : Int)^31 = 2147483648 := by norm_num
    rw [h_q255] at h_i2_lb; rw [h_pow31]; omega
  show (Aeneas.Std.I32.wrapping_sub fe i2).val = _
  rw [Aeneas.Std.I32.wrapping_sub_val_eq, h_i2_val, h_quotient_eq]
  apply Arith.Int.bmod_pow2_eq_of_inBounds' 32 _ (by decide)
  · have h_red : ((2 : Int)^(32-1)) = (2 : Int)^31 := by norm_num
    rw [h_i2_val, h_quotient_eq] at h_sub_lb; rw [h_red]; exact h_sub_lb
  · have h_red : ((2 : Int)^(32-1)) = (2 : Int)^31 := by norm_num
    rw [h_i2_val, h_quotient_eq] at h_sub_ub; rw [h_red]; exact h_sub_ub

/-- **Pure `Int`-level core of the centered Barrett reduction.**

    With `quotient = (v + 2^22) / 2^23` and `r = v - quotient·q`, under `|v| ≤ 2^31 - 2^23`:
    `r ≡ v (mod q)` (trivially, the difference is a multiple of q) and `|r| ≤ 6283009`.

    Bound via the decomposition `r = (v - quotient·2^23) + quotient·(2^23 - q)` where
    `2^23 - q = 8191`, `v - quotient·2^23 ∈ [-2^22, 2^22)` (floor-div remainder), and
    `|quotient| ≤ 255`, giving `|r| ≤ 2^22 + 255·8191 = 6283009`. -/
private theorem reduce_element_core
    (v : Int) (hb : v.natAbs ≤ 2^31 - 2^23) :
    let quotient := (v + (2^22 : Int)) / (2^23 : Int)
    let r := v - quotient * 8380417
    (r : Zq) = (v : Zq) ∧ r.natAbs ≤ 6283009 := by
  -- |v| ≤ 2^31 - 2^23.
  have h_v_abs : |v| ≤ (2^31 - 2^23 : Int) := by
    rw [Int.abs_eq_natAbs]
    have : (v.natAbs : Int) ≤ ((2^31 - 2^23 : Nat) : Int) := by exact_mod_cast hb
    have h2 : ((2^31 - 2^23 : Nat) : Int) = (2^31 - 2^23 : Int) := by norm_num
    omega
  have h_v_lb : -(2139095040 : Int) ≤ v := by
    have h_const : -(2^31 - 2^23 : Int) = -2139095040 := by norm_num
    have := (abs_le.mp h_v_abs).1; rw [h_const] at this; exact this
  have h_v_ub : v ≤ (2139095040 : Int) := by
    have h_const : (2^31 - 2^23 : Int) = 2139095040 := by norm_num
    have := (abs_le.mp h_v_abs).2; rw [h_const] at this; exact this
  set quotient : Int := (v + (2^22 : Int)) / (2^23 : Int) with hq_def
  set r : Int := v - quotient * 8380417 with hr_def
  refine ⟨?_, ?_⟩
  · -- (r : Zq) = (v : Zq) since r = v - quotient·q and (q : Zq) = 0.
    show ((v - quotient * 8380417 : Int) : Zq) = (v : Zq)
    have h_q_zero : ((8380417 : Int) : Zq) = 0 := by
      show ((8380417 : Int) : ZMod Q) = 0
      rw [show (8380417 : Int) = ((Q : Nat) : Int) from by norm_num]
      push_cast
      exact ZMod.natCast_self Q
    rw [Int.cast_sub, Int.cast_mul, h_q_zero, mul_zero, sub_zero]
  · -- |r| ≤ 6283009 via the decomposition r = (v - quotient·2^23) + quotient·8191.
    -- Floor-div remainder: v + 2^22 - quotient·2^23 ∈ [0, 2^23).
    have h_rem_lb : (0 : Int) ≤ (v + 2^22) - quotient * (2^23 : Int) := by
      have h := Int.emod_nonneg (v + 2^22) (by norm_num : (2^23 : Int) ≠ 0)
      have h_decomp : (v + 2^22) % (2^23 : Int) = (v + 2^22) - quotient * (2^23 : Int) := by
        rw [hq_def, Int.emod_def]; ring
      rw [h_decomp] at h; exact h
    have h_rem_ub : (v + 2^22) - quotient * (2^23 : Int) < (2^23 : Int) := by
      have h := Int.emod_lt_of_pos (v + 2^22) (by norm_num : (0 : Int) < 2^23)
      have h_decomp : (v + 2^22) % (2^23 : Int) = (v + 2^22) - quotient * (2^23 : Int) := by
        rw [hq_def, Int.emod_def]; ring
      rw [h_decomp] at h; exact h
    -- So d := v - quotient·2^23 ∈ [-2^22, 2^22).
    set d : Int := v - quotient * (2^23 : Int) with hd_def
    have h_d_lb : -(2^22 : Int) ≤ d := by
      have : (0 : Int) ≤ d + 2^22 := by rw [hd_def]; linarith [h_rem_lb]
      linarith
    have h_d_ub : d < (2^22 : Int) := by
      have : d + 2^22 < (2^23 : Int) := by rw [hd_def]; linarith [h_rem_ub]
      have h_pow : (2^23 : Int) - 2^22 = 2^22 := by norm_num
      linarith [this, h_pow]
    -- |quotient| ≤ 255.
    have h_quot_bounds : -255 ≤ quotient ∧ quotient ≤ 255 := by
      rw [hq_def]
      refine ⟨?_, ?_⟩
      · have h_31_23 : -(2^31 - 2^23 : Int) = -2139095040 := by norm_num
        have h_lb2 : -(2^31 - 2^23 : Int) + 2^22 ≤ v + 2^22 := by
          rw [h_31_23]; linarith [h_v_lb]
        have h := Int.ediv_le_ediv (a := -(2^31 - 2^23 : Int) + 2^22)
                    (b := v + 2^22) (c := (2^23 : Int)) (by norm_num) h_lb2
        have h_const : (-(2^31 - 2^23 : Int) + 2^22) / (2^23 : Int) = -255 := by norm_num
        rw [h_const] at h; omega
      · have h_31_23 : (2^31 - 2^23 : Int) = 2139095040 := by norm_num
        have h_ub2 : v + 2^22 ≤ (2^31 - 2^23 : Int) + 2^22 := by
          rw [h_31_23]; linarith [h_v_ub]
        have h := Int.ediv_le_ediv (a := v + 2^22)
                    (b := (2^31 - 2^23 : Int) + 2^22) (c := (2^23 : Int)) (by norm_num) h_ub2
        have h_const : ((2^31 - 2^23 : Int) + 2^22) / (2^23 : Int) = 255 := by norm_num
        rw [h_const] at h; omega
    -- r = d + quotient·8191  (since 2^23 - q = 8191).
    have h_r_decomp : r = d + quotient * 8191 := by
      rw [hr_def, hd_def]
      have h_2_23 : (2^23 : Int) = 8380417 + 8191 := by norm_num
      have : quotient * (2^23 : Int) = quotient * 8380417 + quotient * 8191 := by
        rw [h_2_23]; ring
      linarith [this]
    -- |r| ≤ 2^22 + 255·8191 = 6283009.
    have h_quot8191_lb : -(255 * 8191 : Int) ≤ quotient * 8191 := by
      have := mul_le_mul_of_nonneg_right h_quot_bounds.1 (by norm_num : (0 : Int) ≤ 8191)
      have h_eq : (-255 : Int) * 8191 = -(255 * 8191 : Int) := by ring
      linarith [this, h_eq]
    have h_quot8191_ub : quotient * 8191 ≤ (255 * 8191 : Int) :=
      mul_le_mul_of_nonneg_right h_quot_bounds.2 (by norm_num : (0 : Int) ≤ 8191)
    have h_r_lb : -(6283009 : Int) ≤ r := by
      rw [h_r_decomp]
      have h_2_22 : -(2^22 : Int) = -4194304 := by norm_num
      have h_255 : (255 * 8191 : Int) = 2088705 := by norm_num
      linarith [h_d_lb, h_quot8191_lb, h_2_22, h_255]
    have h_r_ub : r ≤ (6283009 : Int) := by
      rw [h_r_decomp]
      have h_2_22 : (2^22 : Int) = 4194304 := by norm_num
      have h_255 : (255 * 8191 : Int) = 2088705 := by norm_num
      linarith [h_d_ub, h_quot8191_ub, h_2_22, h_255]
    have h_abs : |r| ≤ (6283009 : Int) := abs_le.mpr ⟨h_r_lb, h_r_ub⟩
    rw [Int.abs_eq_natAbs] at h_abs
    exact_mod_cast h_abs

/-! ## L0 Triple -/

@[spec high]
theorem reduce_element_spec (fe : Std.I32) (h : fe.val.natAbs ≤ 2^31 - 2^23) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.arithmetic.reduce_element fe
    ⦃ ⇓ r => ⌜ liftZ_std r.val = liftZ_std fe.val
              ∧ r.val.natAbs ≤ 6283009 ⌝ ⦄ := by
  apply triple_of_ok_l0 (v := reduce_impl_value fe) (reduce_element_eq_ok fe)
  rw [reduce_impl_value_val fe h]
  -- Goal: liftZ_std (fe.val - q' * 8380417) = liftZ_std fe.val ∧ (…).natAbs ≤ 6283009.
  have h_core := reduce_element_core fe.val h
  refine ⟨?_, h_core.2⟩
  -- liftZ_std x = (x : Zq); reduce to the core's Zq equality.
  show ((fe.val - ((fe.val + (2^22 : Int)) / (2^23 : Int)) * 8380417 : Int) : Zq)
        = (fe.val : Zq)
  exact h_core.1

end libcrux_iot_ml_dsa.Vector.Portable.Arithmetic
