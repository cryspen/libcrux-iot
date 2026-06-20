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
    (value : Std.I64) (hb : value.val.natAbs ≤ 2^31 * 8) :
    (mont_reduce_impl_value value).val
      = let v32 := Int.bmod value.val (2^32)
        let k32 := Int.bmod (v32 * 58728449) (2^32)
        let km  := k32 * 8380417
        value.val / (2^32 : Int) - km / (2^32 : Int) := by
  unfold mont_reduce_impl_value
  set v : Int := value.val
  have h_v_abs : |v| ≤ (2^31 * 8 : Int) := by
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
      have h_lb : -(2^31 * 8 : Int) ≤ v := by
        have := neg_abs_le v; have := h_v_abs; omega
      have h_ediv := Int.ediv_le_ediv (c := 2^32) (by decide) h_lb
      have h_const : -(2^31 * 8 : Int) / 2^32 = -4 := by norm_num
      have h_pow31 : -(2:Int)^(IScalarTy.I32.numBits-1) = -2147483648 := by decide
      rw [h_const] at h_ediv; rw [h_pow31]; omega
    · rw [h_shr]
      have h_ub : v ≤ (2^31 * 8 : Int) := by
        have := le_abs_self v; have := h_v_abs; omega
      have h_ediv := Int.ediv_le_ediv (c := 2^32) (by decide) h_ub
      have h_const : (2^31 * 8 : Int) / 2^32 = 4 := by norm_num
      have h_pow31 : (2:Int)^(IScalarTy.I32.numBits-1) = 2147483648 := by decide
      rw [h_const] at h_ediv; rw [h_pow31]; omega

  -- Final: wrapping_sub vh c
  show (Aeneas.Std.I32.wrapping_sub vh c).bv.toInt = _
  rw [show (Aeneas.Std.I32.wrapping_sub vh c).bv = vh.bv - c.bv from rfl, BitVec.toInt_sub]
  rw [show vh.bv.toInt = vh.val from rfl, show c.bv.toInt = c.val from rfl]
  rw [h_vh_val, h_c_val, h_km_val, h_k_eq_k32]
  apply Arith.Int.bmod_pow2_eq_of_inBounds' 32 _ (by decide)
  · have h_v_div_lb : v / (2^32 : Int) ≥ -4 := by
      have h_lb : -(2^31 * 8 : Int) ≤ v := by
        have := neg_abs_le v; have := h_v_abs; omega
      have h_ediv := Int.ediv_le_ediv (c := 2^32) (by decide) h_lb
      have h_const : -(2^31 * 8 : Int) / 2^32 = -4 := by norm_num
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
  · have h_v_div_ub : v / (2^32 : Int) ≤ 4 := by
      have h_ub : v ≤ (2^31 * 8 : Int) := by
        have := le_abs_self v; have := h_v_abs; omega
      have h_ediv := Int.ediv_le_ediv (c := 2^32) (by decide) h_ub
      have h_const : (2^31 * 8 : Int) / 2^32 = 4 := by norm_num
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
    (v : Int) (hb : v.natAbs ≤ 2^31 * 8) :
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
theorem montgomery_reduce_element_spec (value : Std.I64) (hb : value.val.natAbs ≤ 2^31 * 8) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_reduce_element value
    ⦃ ⇓ r => ⌜ liftZ_std r.val = (value.val : Zq) * (RINV : Zq)
              ∧ r.val.natAbs ≤ 2^31 * 8 ⌝ ⦄ := by
  apply triple_of_ok_l0 (v := mont_reduce_impl_value value) (mont_reduce_element_eq_ok value)
  rw [mont_reduce_impl_value_val value hb]
  set v : Int := value.val
  set v32 := Int.bmod v (2^32)
  set k32 := Int.bmod (v32 * 58728449) (2^32)
  set km := k32 * 8380417
  set res := v / (2^32 : Int) - km / (2^32 : Int)
  have h_k32_lb : -(2^31 : Int) ≤ k32 := (Arith.Int.bmod_pow2_bounds 32 (v32 * 58728449)).1
  have h_k32_ub : k32 < (2^31 : Int) := (Arith.Int.bmod_pow2_bounds 32 (v32 * 58728449)).2
  have h_v_abs : |v| ≤ (2^31 * 8 : Int) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hb
  have h_res_R := mont_reduce_core v hb
  constructor
  · -- Equality clause: (res : Zq) = (v : Zq) * RINV
    show (res : Zq) = (v : Zq) * (RINV : Zq)
    exact mont_reduce_zmod v k32 res h_res_R
  · -- Bound: res.natAbs ≤ 2^31 * 8
    have h_km_abs : |km| ≤ (2^31 : Int) * 8380417 := by
      show |k32 * 8380417| ≤ _; rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_le.mpr ⟨h_k32_lb, le_of_lt h_k32_ub⟩) (by decide)
    have h_res_abs : |res| ≤ (2^31 : Int) * 8 := by
      have h_bound : |res| * (2^32 : Int) ≤ (2^31 : Int) * (8 + 8380417) := by
        calc |res| * (2^32 : Int)
            = |res * (2^32 : Int)| := by rw [abs_mul]; simp
          _ = |v - km| := by rw [h_res_R]
          _ ≤ |v| + |km| := abs_sub v km
          _ ≤ (2^31 : Int) * 8 + (2^31 : Int) * 8380417 := add_le_add h_v_abs h_km_abs
          _ = (2^31 : Int) * (8 + 8380417) := by ring
      have h_div_le := (Int.le_ediv_iff_mul_le (by decide : (0:Int) < 2^32)).mpr h_bound
      have h_const : (2^31 : Int) * (8 + 8380417) / 2^32 = 4190212 := by norm_num
      have h31 : (2:Int)^31 = 2147483648 := by decide
      rw [h_const] at h_div_le; rw [h31]; omega
    rw [Int.abs_eq_natAbs] at h_res_abs; exact_mod_cast h_res_abs

end libcrux_iot_ml_dsa.Vector.Portable.Arithmetic
