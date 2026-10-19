-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCapPosteriorPairRatio

/-! The exact cross-latitude covariance for the original value-conditioned
proper-pure posterior. The two latitudes are independent variables, as is
required for arbitrary Borel bands in source `pc-band-second`. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapPosteriorCrossKernel
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalGaussianJet WholeFieldRegression
open SphericalPosteriorMaps SphericalMarkedWindows SphericalCriticalLatitude
open SphericalTaylorRemainder SphericalParisiConditionedLatitudeCovariance
open SphericalParisiPureLatitudeCovariance
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1000000

def sourceValueTauCross (μ : FiniteMixture) (Q q₁ q₂ s : ℝ) : ℝ :=
  centerCovariance μ Q (q₁*q₂+s)-
    centerCovariance μ Q q₁*centerCovariance μ Q q₂/μ.xi Q-
    centerFirst μ Q q₁*centerFirst μ Q q₂/gradientVariance μ Q*s

/-- Exact physical two-latitude covariance under the original
value/zero-gradient disorder posterior. -/
theorem actual_value_critical_residual_cross_kernel
    (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (w₁ w₂ : Vector (n+1)) {q₁ q₂ s : ℝ}
    (hq₁ : overlap u w₁=q₁) (hq₂ : overlap u w₂=q₂)
    (hρ : overlap w₁ w₂=q₁*q₂+s) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (valueObservation c w₁).comp (valueCriticalCoefficientResidual n μ Q u)
      (((valueObservation c w₂).comp
        (valueCriticalCoefficientResidual n μ Q u)).adjoint 1) =
      (n+1 : ℕ)*sourceValueTauCross μ Q q₁ q₂ s := by
  dsimp only
  rw [value_critical_residual_scalar_kernel n μ hQ u hu,
    value_critical_residual_split n μ hQ u hu,map_sub,map_sub,
    value_value_coupling (by omega) _
      (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le),
    covariancePolynomial_center,covariancePolynomial_mixture,
    center_value_regression_cross n μ hQ u hu w₁ w₂,
    center_gradient_regression_cross (by omega) μ hQ u hu w₁ w₂]
  rw [hq₁,hq₂,hρ]
  unfold sourceValueTauCross centerCovariance gradientVariance centerFirst
  ring_nf

/-- For a pure polynomial, the cross-latitude posterior covariance is
exactly the degree-two-and-higher binomial residual, for both parities. -/
theorem sourceValueTauCross_pure
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : 0 < Q) (q₁ q₂ s : ℝ) :
    sourceValueTauCross (FiniteMixture.pure p hp alpha halpha) Q q₁ q₂ s =
      alpha*Q^p*((q₁*q₂+s)^p-(q₁*q₂)^p-
        (p : ℝ)*(q₁*q₂)^(p-1)*s) := by
  let μ := FiniteMixture.pure p hp alpha halpha
  have hden : alpha*Q^p ≠ 0 := (mul_pos halpha (pow_pos hQ _)).ne'
  have hden₂ : alpha*Q^p*(p : ℝ) ≠ 0 :=
    (mul_pos (mul_pos halpha (pow_pos hQ _))
      (by exact_mod_cast (show 0 < p by omega))).ne'
  unfold sourceValueTauCross gradientVariance
  rw [pure_centerCovariance p hp alpha halpha,
    pure_centerCovariance p hp alpha halpha,
    pure_centerCovariance p hp alpha halpha,
    pure_centerFirst p hp alpha halpha,
    pure_centerFirst p hp alpha halpha,
    pure_centerFirst p hp alpha halpha,
    FiniteMixture.pure_xi]
  simp only [one_pow, mul_one]
  rw [mul_pow, mul_pow]
  field_simp [hden,hden₂]

end
end SlowEquilibration.SourcePureCapPosteriorCrossKernel
