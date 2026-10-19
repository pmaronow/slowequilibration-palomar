-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianQuadraticTrace
public import SlowEquilibration.GaussianRegressionSchur
public import SlowEquilibration.GaussianCovarianceRepresentation

/-! Genuine centered posterior covariance operator and quadratic mean.
The matrix is constructed from the actual coefficient residual, including
singular Gaussian laws; no covariance identity is supplied as a premise. -/
@[expose] public section
namespace SlowEquilibration.GaussianRegressionCovariance
noncomputable section
open Function MeasureTheory ProbabilityTheory GaussianRegression GaussianCovarianceRepresentation
open GaussianQuadraticVariance
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G]

/-- Actual uncentered covariance operator equals the literal residual
Gram, since the genuine residual Gaussian law has mean zero. -/
theorem centeredLaw_covarianceOperator (A : E →L[ℝ] F) (B : E →L[ℝ] G) :
    covarianceOperator (centeredLaw A B)=gram (B.comp (residual A)) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [centered_covarianceOperator_inner _ (centeredLaw_mean A B)]
  rw [centeredLaw,covarianceBilin_map IsGaussian.memLp_two_id,covarianceBilin_stdGaussian,
    innerSL_apply_apply]
  change inner ℝ ((B.comp (residual A)).adjoint x) ((B.comp (residual A)).adjoint y)=
    inner ℝ ((B.comp (residual A)) ((B.comp (residual A)).adjoint x)) y
  rw [ContinuousLinearMap.adjoint_inner_right]

/-- True centered posterior quadratic expectation under an arbitrary
finite Gaussian observation, retaining its actual residual covariance. -/
theorem centeredLaw_quadratic_mean (A : E →L[ℝ] F) (B : E →L[ℝ] G) (S : G →L[ℝ] G) :
    (∫ u,inner ℝ u (S u) ∂centeredLaw A B)=
      LinearMap.trace ℝ G (S.comp (gram (B.comp (residual A)))).toLinearMap := by
  rw [quadratic_integral_eq_trace _ IsGaussian.memLp_two_id,centeredLaw_covarianceOperator]

/-- Actual quadratic mean differs from a scalar covariance trace by no
more than the true residual Gram perturbation. No Gaussian covariance
comparison or mean approximation is assumed. -/
theorem centeredLaw_quadratic_mean_error (A : E →L[ℝ] F) (B : E →L[ℝ] G) (S : G →L[ℝ] G)
    (τ : ℝ) :
    |(∫ u,inner ℝ u (S u) ∂centeredLaw A B)-τ*LinearMap.trace ℝ G S.toLinearMap| ≤
      (Module.finrank ℝ G:ℝ)*‖S‖*‖gram (B.comp (residual A))-τ • ContinuousLinearMap.id ℝ G‖ := by
  rw [centeredLaw_quadratic_mean]
  have heq :
      LinearMap.trace ℝ G (S.comp (gram (B.comp (residual A)))).toLinearMap-
        τ*LinearMap.trace ℝ G S.toLinearMap =
      LinearMap.trace ℝ G (S.comp (gram (B.comp (residual A))-τ • ContinuousLinearMap.id ℝ G)).toLinearMap := by
    rw [ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_smul,ContinuousLinearMap.comp_id]
    simp only [ContinuousLinearMap.toLinearMap_sub,ContinuousLinearMap.toLinearMap_smul,
      map_sub,map_smul,smul_eq_mul]
  rw [heq]
  exact abs_trace_comp_le_dimension_norm S _

end
end SlowEquilibration.GaussianRegressionCovariance

