module

public import SphericalAging.PredictableProductNorm
public import SphericalAging.LpMomentBounds

public section
/-! Product bounds in the actual Lp spaces used by second variations. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace SphericalAging.LpProductBounds
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}
  {f g h u v : α → E}

theorem lpNorm_product_le {G : Type*} [NormedAddCommGroup G] {g : α → G}
    (hf : MemLp f 4 μ) (hg : MemLp g 4 μ) :
    lpNorm (fun q => ‖f q‖*‖g q‖) 2 μ≤lpNorm f 4 μ*lpNorm g 4 μ := by
  have hm : MemLp (fun q => ‖f q‖*‖g q‖) 2 μ := hf.norm.fun_mul hg.norm
  have hp := eLpNorm_smul_le_mul_eLpNorm (p := (4 : ℝ≥0∞)) (q := (4 : ℝ≥0∞))
    (r := (2 : ℝ≥0∞)) hf.aestronglyMeasurable.norm hg.aestronglyMeasurable.norm
  rw [eLpNorm_norm f hf.aestronglyMeasurable,eLpNorm_norm g hg.aestronglyMeasurable] at hp
  change eLpNorm (fun q => ‖f q‖*‖g q‖) 2 μ≤eLpNorm f 4 μ*eLpNorm g 4 μ at hp
  simpa only [ENNReal.toReal_mul,toReal_eLpNorm] using
    ENNReal.toReal_mono (by finiteness : eLpNorm f 4 μ*eLpNorm g 4 μ≠∞) hp

theorem squared_memLp_four (hf : MemLp f 8 μ) : MemLp (fun q => ‖f q‖^2) 4 μ := by
  apply (integrable_norm_rpow_iff (hf.aestronglyMeasurable.norm.pow 2)
    (by norm_num : (4 : ℝ≥0∞)≠0) (by norm_num : (4 : ℝ≥0∞)≠∞)).mp
  simp only [Pi.pow_apply,ENNReal.toReal_ofNat,Real.rpow_ofNat]
  have he (q : α) : ‖‖f q‖^2‖^4=‖f q‖^8 := by rw [Real.norm_of_nonneg (sq_nonneg _),← pow_mul]
  simp_rw [he]
  exact hf.integrable_norm_pow (by norm_num)

theorem lpNorm_squared_four (hf : MemLp f 8 μ) :
    lpNorm (fun q => ‖f q‖^2) 4 μ=(lpNorm f 8 μ)^2 := by
  have he := eLpNorm_norm_rpow f hf.aestronglyMeasurable (by norm_num : (0 : ℝ)<2) (p := (4 : ℝ≥0∞))
  have hc : (4 : ℝ≥0∞)*ENNReal.ofReal (2 : ℝ)=8 := by norm_num
  rw [hc] at he
  simpa only [Real.rpow_ofNat,ENNReal.rpow_ofNat,ENNReal.toReal_pow,toReal_eLpNorm] using congrArg ENNReal.toReal he

theorem lpNorm_squared_product_le (hf : MemLp f 8 μ) (hg : MemLp g 4 μ) :
    lpNorm (fun q => ‖f q‖^2*‖g q‖) 2 μ≤(lpNorm f 8 μ)^2*lpNorm g 4 μ := by
  have hp := lpNorm_product_le (squared_memLp_four hf) hg
  rw [lpNorm_squared_four hf] at hp
  simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hp

theorem lpNorm_three_products_le (R : α → ℝ) (hR : MemLp R 2 μ)
    (hf : MemLp f 8 μ) (hg : MemLp g 4 μ) (hh : MemLp h 4 μ)
    (hu : MemLp u 4 μ) (hv : MemLp v 4 μ) (M L : ℝ) (hM : 0≤M) (hL : 0≤L)
    (hbound : ∀ᵐ q ∂μ,‖R q‖≤M*‖f q‖^2*‖g q‖+L*‖h q‖*‖g q‖+L*‖u q‖*‖v q‖) :
    lpNorm R 2 μ≤M*(lpNorm f 8 μ)^2*lpNorm g 4 μ+
      L*lpNorm h 4 μ*lpNorm g 4 μ+L*lpNorm u 4 μ*lpNorm v 4 μ := by
  let A : α → ℝ := fun q => ‖f q‖^2*‖g q‖
  let B : α → ℝ := fun q => ‖h q‖*‖g q‖
  let C : α → ℝ := fun q => ‖u q‖*‖v q‖
  have hA : MemLp A 2 μ := (squared_memLp_four hf).fun_mul hg.norm
  have hB : MemLp B 2 μ := hh.norm.fun_mul hg.norm
  have hC : MemLp C 2 μ := hu.norm.fun_mul hv.norm
  have hp : eLpNorm R 2 μ≤eLpNorm (M • A+L • B+L • C) 2 μ := by
    apply eLpNorm_mono_ae hR.aestronglyMeasurable
    filter_upwards [hbound] with q hq
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    have hs : 0≤M*A q+L*B q+L*C q := by dsimp [A,B,C];positivity
    rw [Real.norm_of_nonneg hs]
    simpa only [A,B,C,mul_assoc] using hq
  have hsum : MemLp (M • A+L • B+L • C) 2 μ := ((hA.const_smul M).add (hB.const_smul L)).add (hC.const_smul L)
  have hnorm : lpNorm R 2 μ≤lpNorm (M • A+L • B+L • C) 2 μ :=
    ENNReal.toReal_mono hsum.eLpNorm_ne_top hp
  calc
    _ ≤ lpNorm (M • A+L • B+L • C) 2 μ := hnorm
    _ ≤ lpNorm (M • A) 2 μ+lpNorm (L • B) 2 μ+lpNorm (L • C) 2 μ :=
      (lpNorm_add_le ((hA.const_smul M).add (hB.const_smul L)) (by norm_num)).trans
        (add_le_add (lpNorm_add_le (hA.const_smul M) (by norm_num)) (le_refl _))
    _ = M*lpNorm A 2 μ+L*lpNorm B 2 μ+L*lpNorm C 2 μ := by
      simp only [lpNorm_const_smul,coe_nnnorm,Real.norm_of_nonneg hM,Real.norm_of_nonneg hL]
    _ ≤ _ := by
      dsimp [A,B,C]
      simpa only [mul_assoc] using add_le_add (add_le_add (mul_le_mul_of_nonneg_left (lpNorm_squared_product_le hf hg) hM)
        (mul_le_mul_of_nonneg_left (lpNorm_product_le hh hg) hL))
        (mul_le_mul_of_nonneg_left (lpNorm_product_le hu hv) hL)

end SphericalAging.LpProductBounds
