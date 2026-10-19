-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianNormMean
public import Lemmas.SpinGlass.gaussian_concentration

/-! Sharp Gaussian norm concentration about the dimension bound for the
actual standard Gaussian law. -/

@[expose] public section
namespace SlowEquilibration.GaussianNormConcentration
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology

theorem centered_lipschitz_mgf_le {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hLip : LipschitzWith L.toNNReal F) (t : ℝ) :
    mgf (fun x => F x - ∫ y, F y ∂SYK.standardGaussianMeasureOnEuclidean ι)
      (SYK.standardGaussianMeasureOnEuclidean ι) t ≤ Real.exp (L^2*t^2/2) := by
  rcases hL.eq_or_lt with hL | hL
  · subst L
    have hf : F = fun _ => F 0 := by
      funext x
      have h := hLip.dist_le_mul x 0
      simpa only [Real.toNNReal_zero, NNReal.coe_zero, zero_mul, dist_le_zero] using h
    rw [hf]
    simp [mgf]
  · exact SYK.product_standardGaussian_mgf_le F L hL hLip t

theorem centered_lipschitz_upper_tail {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hLip : LipschitzWith L.toNNReal F) {s : ℝ} (hs : 0 ≤ s) :
    (SYK.standardGaussianMeasureOnEuclidean ι).real
      {x | (∫ y, F y ∂SYK.standardGaussianMeasureOnEuclidean ι)+s ≤ F x} ≤
        Real.exp (-s^2/(2*L^2)) := by
  rcases hL.eq_or_lt with hL | hL
  · subst L
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, div_zero, Real.exp_zero]
    exact measureReal_le_one
  · have ht := (SYK.product_standardGaussian_hasSubgaussianMGF F L hL hLip).measure_ge_le hs
    rw [Real.coe_toNNReal _ (sq_nonneg L)] at ht
    refine (measureReal_mono (fun x hx => ?_)).trans ht
    change s ≤ F x - _
    change (∫ y, F y ∂SYK.standardGaussianMeasureOnEuclidean ι)+s ≤ F x at hx
    linarith

theorem standardGaussian_norm_upper_tail_real {ι : Type*} [Fintype ι]
    {s : ℝ} (hs : 0 ≤ s) :
    (SYK.standardGaussianMeasureOnEuclidean ι).real
      {g | Real.sqrt (Fintype.card ι : ℝ)+s ≤ ‖g‖} ≤ Real.exp (-s^2/2) := by
  have hl : LipschitzWith ((1 : ℝ).toNNReal) (fun g : EuclideanSpace ℝ ι => ‖g‖) := by
    simpa using (lipschitzWith_one_norm : LipschitzWith 1 (fun g : EuclideanSpace ℝ ι => ‖g‖))
  have hmgf := SYK.product_standardGaussian_hasSubgaussianMGF
    (fun g : EuclideanSpace ℝ ι => ‖g‖) 1 (by norm_num) hl
  have ht := hmgf.measure_ge_le hs
  norm_num at ht
  have hm := GaussianNormMean.standardGaussian_integral_norm_le_sqrt_card ι
  refine (measureReal_mono (fun g hg => ?_)).trans ht
  change s ≤ ‖g‖ - _
  change Real.sqrt (Fintype.card ι : ℝ)+s ≤ ‖g‖ at hg
  linarith

theorem standardGaussian_norm_upper_tail {ι : Type*} [Fintype ι]
    {s : ℝ} (hs : 0 ≤ s) :
    (SYK.standardGaussianMeasureOnEuclidean ι)
      {g | Real.sqrt (Fintype.card ι : ℝ)+s ≤ ‖g‖} ≤
        ENNReal.ofReal (Real.exp (-s^2/2)) := by
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  exact standardGaussian_norm_upper_tail_real hs

end
end SlowEquilibration.GaussianNormConcentration
