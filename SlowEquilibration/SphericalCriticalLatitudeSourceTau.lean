-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalCriticalLatitudeScoreMean
public import SlowEquilibration.SphericalCriticalLatitudeGradientCross

/-! The source tau_r is the genuine covariance of the actual full-field
critical-point coefficient residual. Its degree-zero coefficient is proved
nonnegative by an actual regression variance, with no covariance premise. -/

@[expose] public section
namespace SlowEquilibration.SphericalCriticalLatitude
noncomputable section
open MeasureTheory ProbabilityTheory Function
open SphericalModel SphericalGaussianJet WholeFieldRegression SphericalPosteriorMaps
open SphericalTaylorRemainder SphericalSequentialRegression SphericalMarkedWindows
open SphericalTwoPointCovariance GaussianRegression IntrinsicGradientRegression
open SphericalParisiConditionedLatitudeCovariance GaussianContinuousFieldLaw
open SphericalKacRiceGluing
open scoped RealInnerProductSpace Matrix
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem center_score_regression_cross {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (u : Vector N) (hu : ‖u‖^2=(N : ℝ)) (w₁ w₂ : Vector N) {r : ℝ}
    (hr₁ : overlap u w₁=r) (hr₂ : overlap u w₂=r) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    valueObservation c w₁ (lift (scoreCLM c u)
      (scoreCLM c u ((valueObservation c w₂).adjoint 1)))=
      (N : ℝ)*sourceScoreCorrection μ Q r := by
  dsimp only
  rw [center_score_value_cross hN μ hQ.le u w₂,hr₂]
  change valueObservation (centerCoefficients (mixtureCoefficients μ) Q) w₁
    (lift (scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) u)
      ((N : ℝ) • scorePairEquiv (centerCovariance μ Q r,r*centerFirst μ Q r)))=_
  rw [center_value_score_lift hN μ hQ hnp u hu w₁,hr₁]
  rfl

/-- Source10.12(a), its literal finite-volume residual covariance. The
overlap hypotheses are exact geometric coordinates of the actual points. -/
theorem actual_critical_residual_kernel_eq_sourceTau (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (w₁ w₂ : Vector (n+1)) {r t : ℝ}
    (hr₁ : overlap u w₁=r) (hr₂ : overlap u w₂=r)
    (hρ : overlap w₁ w₂=r^2+(1-r^2)*t) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (valueObservation c w₁).comp (criticalCoefficientResidual n μ Q u)
      (((valueObservation c w₂).comp (criticalCoefficientResidual n μ Q u)).adjoint 1)=
      (n+1 : ℕ)*sourceTau μ Q r t := by
  dsimp only
  rw [critical_residual_scalar_kernel n μ hQ hnp u hu,
    critical_residual_split n μ hQ u hu,map_sub,map_sub,
    value_value_coupling (by omega) _
      (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le),
    covariancePolynomial_center,covariancePolynomial_mixture,
    center_score_regression_cross (by omega) μ hQ hnp u hu w₁ w₂ hr₁ hr₂,
    center_gradient_regression_cross (by omega) μ hQ u hu w₁ w₂]
  rw [hr₁,hr₂,hρ]
  unfold sourceTau centerCovariance gradientVariance centerFirst
  rw [mul_one]
  ring

/-- Source10.12(b), degree-zero nonnegativity follows from the true
variance of the radially scaled actual coefficient field. -/
theorem sourceTau_zero_nonneg (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (r : ℝ) : 0 ≤ sourceTau μ Q r 0 := by
  let u := southPole 0
  have hu : ‖u‖^2=(1 : ℕ) := southPole_norm_sq 0
  have hr : overlap u (r • u)=r := by
    simp only [overlap,real_inner_smul_right,real_inner_self_eq_norm_sq,hu,
      Nat.zero_add,Nat.cast_one,div_one,mul_one]
  have hρ : overlap (r • u) (r • u)=r^2+(1-r^2)*0 := by
    simp only [overlap,real_inner_self_eq_norm_sq,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
      hu,Nat.zero_add,Nat.cast_one,div_one,mul_one,mul_zero,add_zero]
  have hk := actual_critical_residual_kernel_eq_sourceTau 0 μ hQ hnp u hu
    (r • u) (r • u) hr hr hρ
  dsimp only at hk
  simp only [Nat.zero_add,Nat.cast_one,one_mul] at hk
  let f := (valueObservation (centerCoefficients (mixtureCoefficients μ) Q) (r • u)).comp
    (criticalCoefficientResidual 0 μ Q u)
  have hn : 0 ≤ f (f.adjoint 1) := by
    have he : f (f.adjoint 1)=inner ℝ (f.adjoint 1) (f.adjoint 1) := by
      rw [f.adjoint_inner_left]
      simp only [RCLike.inner_apply,RCLike.conj_to_real,mul_one]
    rw [he,real_inner_self_eq_norm_sq]
    positivity
  exact hk ▸ hn

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

omit [CompactSpace K] in
/-- The actual centered continuous process has the literal source
tau_r covariance at every pair of actual latitude parameters. -/
theorem actual_critical_continuous_covariance_eq_sourceTau (n : ℕ)
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (z : K → Vector (n+1)) (hz : Continuous z) (v w : K) {r t : ℝ}
    (hrv : overlap u (z v)=r) (hrw : overlap u (z w)=r)
    (hρ : overlap (z v) (z w)=r^2+(1-r^2)*t) :
    cov[fun g => criticalContinuousResidual n μ Q u z hz g v,
      fun g => criticalContinuousResidual n μ Q u z hz g w;
        stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)]=
      (n+1 : ℕ)*sourceTau μ Q r t := by
  rw [criticalContinuousResidual_covariance n μ hQ hnp u hu z hz v w]
  have hk := actual_critical_residual_kernel_eq_sourceTau n μ hQ hnp u hu
    (z v) (z w) hrv hrw hρ
  dsimp only at hk
  rwa [critical_residual_scalar_kernel n μ hQ hnp u hu] at hk

end
end SlowEquilibration.SphericalCriticalLatitude
