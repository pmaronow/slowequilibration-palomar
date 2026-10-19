-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Probability.Moments.Variance

/-! Actual weighted mean comparison by the centered square fluctuation.
This isolates the elementary covariance step used after the exact GOE
adjugate expectation and actual exceptional-event estimate. -/
@[expose] public section
namespace SlowEquilibration.WeightedTraceMean
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma abs_integral_mul_le_sqrt {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {F G : Ω → ℝ} (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    |∫ x,F x*G x ∂μ| ≤ Real.sqrt (∫ x,F x^2 ∂μ)*Real.sqrt (∫ x,G x^2 ∂μ) := by
  have hh:=integral_mul_norm_le_Lp_mul_Lq
    (show (2:ℝ).HolderConjugate 2 by rw [Real.holderConjugate_iff];norm_num)
    (by simpa using hF) (by simpa using hG)
  have hn : |∫ x,F x*G x ∂μ| ≤ ∫ x,‖F x‖*‖G x‖ ∂μ := by
    simpa only [Real.norm_eq_abs,norm_mul] using norm_integral_le_integral_norm (fun x=>F x*G x)
  exact hn.trans (by simpa only [Real.norm_eq_abs,Real.rpow_two,sq_abs,← Real.sqrt_eq_rpow] using hh)

/-- The mean of an actual observable differs from its mean under an
integrable weight of expectation one by a proved square-moment bound. -/
theorem mean_minus_weighted_mean_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {D X : Ω → ℝ}
    (hD : MemLp D 2 μ) (hX : MemLp X 2 μ) (hDmean : (∫ x,D x ∂μ)=1) :
    |(∫ x,X x ∂μ)-(∫ x,D x*X x ∂μ)| ≤
      Real.sqrt (∫ x,D x^2 ∂μ)*
        Real.sqrt (∫ x,(X x-∫ y,X y ∂μ)^2 ∂μ) := by
  have hXi:=hX.integrable (by norm_num : (1:ℝ≥0∞)≤2)
  have hDi:=hD.integrable (by norm_num : (1:ℝ≥0∞)≤2)
  have hDX : Integrable (fun x=>D x*X x) μ:=hD.integrable_mul hX
  have hXm : MemLp (fun x=>X x-∫ y,X y ∂μ) 2 μ:=hX.sub (memLp_const _)
  have he : (∫ x,D x*(X x-∫ y,X y ∂μ) ∂μ)=
      (∫ x,D x*X x ∂μ)-(∫ y,X y ∂μ) := by
    simp only [mul_sub]
    rw [integral_sub hDX (hDi.mul_const _),integral_mul_const,hDmean,one_mul]
  have hh:=abs_integral_mul_le_sqrt hD hXm
  rw [he,abs_sub_comm] at hh
  exact hh

end
end SlowEquilibration.WeightedTraceMean
