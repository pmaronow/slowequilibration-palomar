-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalValueCriticalLatitudeContinuousLaw

/-! Exact scalar-value conditioning of the actual center field, with its
proper mean and residual covariance. There is no two-dimensional score
inverse, so the result applies directly to the physical pure posterior. -/

@[expose] public section
namespace SlowEquilibration.SphericalCriticalLatitude
noncomputable section
open MeasureTheory ProbabilityTheory Function
open SphericalModel SphericalGaussianJet WholeFieldRegression SphericalPosteriorMaps
open SphericalTaylorRemainder SphericalSequentialRegression SphericalMarkedWindows
open GaussianRegression IntrinsicGradientRegression SphericalTwoPointCovariance
open GaussianContinuousFieldLaw SphericalParisiConditionedLatitudeCovariance
open scoped RealInnerProductSpace
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- True physical value precision, proved for every actual finite mixture. -/
theorem center_physical_value_inverse_apply (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ)) (b : ℝ) :
    (gram (valueCLM (centerCoefficients (mixtureCoefficients μ) Q) u)).inverse b=
      b/((n+1 : ℕ)*μ.xi Q) := by
  let A := valueCLM (centerCoefficients (mixtureCoefficients μ) Q) u
  have hA := center_value_surjective μ hQ u hu
  have hg := center_value_gram (by omega) μ hQ.le u hu
  have he := congrArg (fun T => T ((gram A).inverse b)) hg
  have hh : (n+1 : ℕ)*μ.xi Q*(gram A).inverse b=b :=
    he.symm.trans ((gram_isInvertible A hA).self_apply_inverse b)
  apply (eq_div_iff (mul_pos (by positivity) (μ.xi_pos hQ)).ne').mpr
  simpa only [mul_comm] using hh

private theorem scalar_value_adjoint {N P : ℕ} (f A : EuclideanDisorder N P →L[ℝ] ℝ)
    (b : ℝ) : f (A.adjoint b)=b*A (f.adjoint 1) := by
  have h : f (A.adjoint b)=inner ℝ (f.adjoint 1) (A.adjoint b) := by
    rw [f.adjoint_inner_left]
    simp only [RCLike.inner_apply,RCLike.conj_to_real,mul_one]
  rw [h,A.adjoint_inner_right,RCLike.inner_apply,RCLike.conj_to_real]

/-- The literal actual value/zero-gradient conditional mean is
N e xi_Q(r)/xi_Q(1), including the proper pure case. -/
theorem center_value_only_lift (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (w : Vector (n+1)) (e : ℝ) :
    valueObservation (centerCoefficients (mixtureCoefficients μ) Q) w
      (lift (valueCLM (centerCoefficients (mixtureCoefficients μ) Q) u) ((n+1 : ℕ)*e))=
      (n+1 : ℕ)*μ.xi (Q*overlap u w)/μ.xi Q*e := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hc := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  change valueObservation c w ((valueCLM c u).adjoint
    ((gram (valueCLM c u)).inverse ((n+1 : ℕ)*e)))=_
  rw [scalar_value_adjoint,center_physical_value_inverse_apply n μ hQ u hu]
  change ((n+1 : ℕ)*e/((n+1 : ℕ)*μ.xi Q))*
    valueObservation c u ((valueObservation c w).adjoint 1)=_
  rw [value_value_coupling (by omega) c hc,covariancePolynomial_center,covariancePolynomial_mixture]
  field_simp [(μ.xi_pos hQ).ne',show ((n+1 : ℕ) : ℝ)≠0 by positivity]

theorem center_value_regression_cross (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (w₁ w₂ : Vector (n+1)) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    valueObservation c w₁ (lift (valueCLM c u)
      (valueCLM c u ((valueObservation c w₂).adjoint 1)))=
      (n+1 : ℕ)*μ.xi (Q*overlap u w₁)*μ.xi (Q*overlap u w₂)/μ.xi Q := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hc := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hv : valueCLM c u ((valueObservation c w₂).adjoint 1)=
      (n+1 : ℕ)*μ.xi (Q*overlap u w₂) := by
    change valueObservation c u ((valueObservation c w₂).adjoint 1)=_
    rw [value_value_coupling (by omega) c hc,covariancePolynomial_center,covariancePolynomial_mixture]
  rw [hv,center_value_only_lift n μ hQ u hu w₁]
  ring

/-- The proper value/zero-gradient residual covariance, derived directly
from scalar-value and true tangent-gradient regression. -/
theorem actual_value_critical_residual_kernel (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (w₁ w₂ : Vector (n+1)) {r t : ℝ}
    (hr₁ : overlap u w₁=r) (hr₂ : overlap u w₂=r)
    (hρ : overlap w₁ w₂=r^2+(1-r^2)*t) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (valueObservation c w₁).comp (valueCriticalCoefficientResidual n μ Q u)
      (((valueObservation c w₂).comp (valueCriticalCoefficientResidual n μ Q u)).adjoint 1)=
      (n+1 : ℕ)*(centerCovariance μ Q (r^2+(1-r^2)*t)-
        (centerCovariance μ Q r)^2/μ.xi Q-
        (1-r^2)*(centerFirst μ Q r)^2/gradientVariance μ Q*t) := by
  dsimp only
  rw [value_critical_residual_scalar_kernel n μ hQ u hu,
    value_critical_residual_split n μ hQ u hu,map_sub,map_sub,
    value_value_coupling (by omega) _
      (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le),
    covariancePolynomial_center,covariancePolynomial_mixture,
    center_value_regression_cross n μ hQ u hu w₁ w₂,
    center_gradient_regression_cross (by omega) μ hQ u hu w₁ w₂]
  rw [hr₁,hr₂,hρ]
  unfold centerCovariance gradientVariance centerFirst
  rw [mul_one]
  ring

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

omit [CompactSpace K] in
theorem valueCriticalContinuousMean_eq_source (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (z : K → Vector (n+1)) (hz : Continuous z) (e : ℝ) (v : K) :
    valueCriticalContinuousMean n μ Q u z hz e v=
      (n+1 : ℕ)*μ.xi (Q*overlap u (z v))/μ.xi Q*e := by
  unfold valueCriticalContinuousMean criticalContinuousField
  rw [modelContinuousField_apply,valueLift_eq n μ hQ.le u hu]
  exact center_value_only_lift n μ hQ u hu (z v) e

omit [CompactSpace K] in
theorem actual_value_critical_continuous_covariance (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (z : K → Vector (n+1)) (hz : Continuous z) (v w : K) {r t : ℝ}
    (hrv : overlap u (z v)=r) (hrw : overlap u (z w)=r)
    (hρ : overlap (z v) (z w)=r^2+(1-r^2)*t) :
    cov[fun g => valueCriticalContinuousResidual n μ Q u z hz g v,
      fun g => valueCriticalContinuousResidual n μ Q u z hz g w;
        stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)]=
      (n+1 : ℕ)*(centerCovariance μ Q (r^2+(1-r^2)*t)-
        (centerCovariance μ Q r)^2/μ.xi Q-
        (1-r^2)*(centerFirst μ Q r)^2/gradientVariance μ Q*t) := by
  rw [evaluation_covariance]
  change (valueObservation (centerCoefficients (mixtureCoefficients μ) Q) (z v)).comp
    (valueCriticalCoefficientResidual n μ Q u)
      (((valueObservation (centerCoefficients (mixtureCoefficients μ) Q) (z w)).comp
        (valueCriticalCoefficientResidual n μ Q u)).adjoint 1)=_
  exact actual_value_critical_residual_kernel n μ hQ u hu (z v) (z w) hrv hrw hρ

end
end SlowEquilibration.SphericalCriticalLatitude
