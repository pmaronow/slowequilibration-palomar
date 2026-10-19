-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianPosteriorQuadraticMean

/-! Genuine centered Gaussian norm second moment from its literal
covariance, without an ambient coefficient dimension or norm-MGF input. -/
@[expose] public section
namespace SlowEquilibration.GaussianQuadraticVariance
noncomputable section
open Function MeasureTheory ProbabilityTheory GaussianCovarianceRepresentation
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem centered_gaussian_norm_second_moment (μ : Measure E) [IsGaussian μ]
    (hmean : ∫ x,x ∂μ=0) (τ : ℝ) (hcov : ∀ x:E,covarianceBilin μ x x ≤ τ*‖x‖^2) :
    Integrable (fun x:E=>‖x‖^2) μ ∧ (∫ x,‖x‖^2 ∂μ) ≤ (Module.finrank ℝ E:ℝ)*τ := by
  have hLp : MemLp (fun x:E=>‖x‖) 2 μ:=by simpa only [id_eq] using (IsGaussian.memLp_two_id (μ:=μ)).norm
  have hi : Integrable (fun x:E=>‖x‖^2) μ:=
    (memLp_two_iff_integrable_sq (by fun_prop)).mp hLp
  refine ⟨hi,?_⟩
  have he : (∫ x,‖x‖^2 ∂μ)=LinearMap.trace ℝ E (covarianceOperator μ).toLinearMap := by
    have hh:=quadratic_integral_eq_trace μ IsGaussian.memLp_two_id (ContinuousLinearMap.id ℝ E)
    simpa only [ContinuousLinearMap.id_apply,real_inner_self_eq_norm_sq,ContinuousLinearMap.id_comp] using hh
  rw [he,clm_trace_eq_sum_inner (stdOrthonormalBasis ℝ E)]
  calc
    _ ≤ ∑ _i:Fin (Module.finrank ℝ E),τ := by
      apply Finset.sum_le_sum
      intro i hi
      have hh:=hcov (stdOrthonormalBasis ℝ E i)
      rw [real_inner_comm,centered_covarianceOperator_inner μ hmean]
      simpa only [OrthonormalBasis.norm_eq_one,one_pow,mul_one] using hh
    _=_ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

end
end SlowEquilibration.GaussianQuadraticVariance

