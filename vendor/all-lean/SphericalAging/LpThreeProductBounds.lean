module

public import SphericalAging.LpProductBounds

public section
/-! Mixed fourth/eighth product estimates for continuous Hessian sources. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal
namespace SphericalAging.LpThreeProductBounds
set_option backward.isDefEq.respectTransparency false
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}
  {f g h : α → E}

instance holderEightEightFour : ENNReal.HolderTriple (8 : ℝ≥0∞) 8 4 := ⟨by
  change ((8 : ℝ≥0) : ℝ≥0∞)⁻¹+((8 : ℝ≥0) : ℝ≥0∞)⁻¹=((4 : ℝ≥0) : ℝ≥0∞)⁻¹
  rw [←ENNReal.coe_inv (by norm_num : (8 : ℝ≥0)≠0),
    ←ENNReal.coe_inv (by norm_num : (4 : ℝ≥0)≠0),←ENNReal.coe_add]
  exact_mod_cast (by norm_num : (8 : ℝ≥0)⁻¹+(8 : ℝ≥0)⁻¹=(4 : ℝ≥0)⁻¹)⟩

theorem lpNorm_eight_product_le (hf : MemLp f 8 μ) (hg : MemLp g 8 μ) :
    lpNorm (fun q => ‖f q‖*‖g q‖) 4 μ≤lpNorm f 8 μ*lpNorm g 8 μ := by
  have hp := eLpNorm_smul_le_mul_eLpNorm (p := (8 : ℝ≥0∞)) (q := (8 : ℝ≥0∞))
    (r := (4 : ℝ≥0∞)) hf.aestronglyMeasurable.norm hg.aestronglyMeasurable.norm
  rw [eLpNorm_norm f hf.aestronglyMeasurable,eLpNorm_norm g hg.aestronglyMeasurable] at hp
  change eLpNorm (fun q => ‖f q‖*‖g q‖) 4 μ≤eLpNorm f 8 μ*eLpNorm g 8 μ at hp
  simpa only [ENNReal.toReal_mul,toReal_eLpNorm] using
    ENNReal.toReal_mono (by finiteness : eLpNorm f 8 μ*eLpNorm g 8 μ≠∞) hp

theorem lpNorm_triple_le (hf : MemLp f 4 μ) (hg : MemLp g 8 μ) (hh : MemLp h 8 μ) :
    lpNorm (fun q => ‖f q‖*‖g q‖*‖h q‖) 2 μ≤lpNorm f 4 μ*lpNorm g 8 μ*lpNorm h 8 μ := by
  have hp := LpProductBounds.lpNorm_product_le hf (hg.norm.fun_mul hh.norm)
  have hnorm (q : α) : ‖‖g q‖*‖h q‖‖=‖g q‖*‖h q‖ :=
    Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  simp_rw [hnorm,←mul_assoc] at hp
  exact hp.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (lpNorm_eight_product_le hg hh) (lpNorm_nonneg : 0≤lpNorm f 4 μ))

theorem lpNorm_dominated_sum_le (R A B C : α → ℝ) (hR : MemLp R 2 μ)
    (hA : MemLp A 2 μ) (hB : MemLp B 2 μ) (hC : MemLp C 2 μ)
    (hpos : ∀ q,0≤A q+B q+C q) (hb : ∀ᵐ q ∂μ,‖R q‖≤A q+B q+C q) :
    lpNorm R 2 μ≤lpNorm A 2 μ+lpNorm B 2 μ+lpNorm C 2 μ := by
  have hm : MemLp (A+B+C) 2 μ := (hA.add hB).add hC
  have he : eLpNorm R 2 μ≤eLpNorm (A+B+C) 2 μ := by
    apply eLpNorm_mono_ae hR.aestronglyMeasurable
    filter_upwards [hb] with q hq
    simpa only [Pi.add_apply,Real.norm_of_nonneg (hpos q)] using hq
  have hn : lpNorm R 2 μ≤lpNorm (A+B+C) 2 μ := ENNReal.toReal_mono hm.eLpNorm_ne_top he
  exact hn.trans ((lpNorm_add_le (hA.add hB) (by norm_num)).trans
    (add_le_add (lpNorm_add_le hA (by norm_num)) (le_refl _)))
end SphericalAging.LpThreeProductBounds
