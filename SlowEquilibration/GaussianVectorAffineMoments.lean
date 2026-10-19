-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianVectorPolynomialMoments

/-! Genuine ordinary norm moments after deterministic Gaussian mean
shifts, retaining the true covariance and dimension bounds. -/
@[expose] public section
namespace SlowEquilibration.GaussianVectorPolynomialMoments
noncomputable section
open Function MeasureTheory ProbabilityTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_add_power_le (x m : E) (r : ℕ) : ‖x+m‖^r ≤ (2:ℝ)^r*(‖x‖^r+‖m‖^r) := by
  by_cases h : ‖x‖ ≤ ‖m‖
  · have hb : ‖x+m‖ ≤ 2*‖m‖:=(norm_add_le x m).trans (by linarith)
    calc
      _ ≤ (2*‖m‖)^r:=pow_le_pow_left₀ (norm_nonneg _) hb _
      _=(2:ℝ)^r*‖m‖^r:=mul_pow _ _ _
      _ ≤ _:=mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (pow_nonneg (norm_nonneg x) r)) (by positivity)
  · have hb : ‖x+m‖ ≤ 2*‖x‖:=(norm_add_le x m).trans (by linarith)
    calc
      _ ≤ (2*‖x‖)^r:=pow_le_pow_left₀ (norm_nonneg _) hb _
      _=(2:ℝ)^r*‖x‖^r:=mul_pow _ _ _
      _ ≤ _:=mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (pow_nonneg (norm_nonneg m) r)) (by positivity)

/-- True affine Gaussian norm moments are uniformly bounded once the
covariance scale and actual deterministic mean norm are bounded. -/
theorem affine_gaussian_norm_moments (μ : Measure E) [IsGaussian μ]
    (hmean : ∫ x,x ∂μ=0) {σ A M : ℝ} (hσ : 0 < σ)
    (hcov : ∀ x:E,covarianceBilin μ x x ≤ σ^2*‖x‖^2)
    (hscale : σ*Real.sqrt (Module.finrank ℝ E:ℝ) ≤ A)
    (m : E) (_hM : 0 ≤ M) (hm : ‖m‖ ≤ M) :
    ∀ r:ℕ,Integrable (fun x:E=>‖x+m‖^r) μ ∧
      (∫ x,‖x+m‖^r ∂μ) ≤ (2:ℝ)^r*((r.factorial:ℝ)*Real.exp (A+σ^2/2)+M^r) := by
  intro r
  have hbase:=centered_gaussian_norm_moments μ hmean hσ hcov hscale r
  have hmPow : ‖m‖^r ≤ M^r:=pow_le_pow_left₀ (norm_nonneg _) hm _
  have hbound (x:E) : ‖x+m‖^r ≤ (2:ℝ)^r*(‖x‖^r+M^r) :=
    (norm_add_power_le x m r).trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hmPow) (by positivity))
  have hdom : Integrable (fun x:E=>(2:ℝ)^r*(‖x‖^r+M^r)) μ:=
    (hbase.1.add (integrable_const (M^r))).const_mul _
  have hint : Integrable (fun x:E=>‖x+m‖^r) μ:=hdom.mono'
    ((continuous_id.add continuous_const).norm.pow r).measurable.aestronglyMeasurable
    (ae_of_all _ (fun x=>by simpa only [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)] using hbound x))
  refine ⟨hint,?_⟩
  have hh:=integral_mono_ae hint hdom (ae_of_all _ hbound)
  change (∫ x,‖x+m‖^r ∂μ) ≤ ∫ x,(2:ℝ)^r*(‖x‖^r+M^r) ∂μ at hh
  rw [integral_const_mul,integral_add hbase.1 (integrable_const _),integral_const,probReal_univ,one_smul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add hbase.2 le_rfl) (by positivity))

end
end SlowEquilibration.GaussianVectorPolynomialMoments
