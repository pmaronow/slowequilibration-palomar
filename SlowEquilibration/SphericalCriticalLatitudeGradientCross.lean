-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalCriticalLatitudeResidualCovariance
public import SlowEquilibration.CenterCovarianceDerivativeScaling

/-! Exact tangent-gradient contractions in the literal critical posterior.
The physical gradient observation and its covariance inverse are used
directly, including every dimension and center-overlap factor. -/

@[expose] public section
namespace SlowEquilibration.SphericalCriticalLatitude
noncomputable section
open MeasureTheory ProbabilityTheory Function
open SphericalModel SphericalGaussianJet WholeFieldRegression SphericalPosteriorMaps
open SphericalTaylorRemainder SphericalSequentialRegression SphericalMarkedWindows
open SphericalTwoPointCovariance GaussianRegression IntrinsicGradientRegression SphericalForm
open SphericalAging.HardSphereDynamics
open scoped RealInnerProductSpace
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal covariance vector between the complete tangent gradient
and a field value at an arbitrary point. -/
theorem center_gradient_value_cross {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (u w : Vector N) :
    intrinsicGamma (centerCoefficients (mixtureCoefficients μ) Q) u
      ((valueObservation (centerCoefficients (mixtureCoefficients μ) Q) w).adjoint 1)=
      (Q*μ.xi1 (Q*overlap u w)) • (tangentPlane u).orthogonalProjectionOnto w := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hc := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ
  apply ext_inner_left ℝ
  intro v
  rw [intrinsicGamma_inner,real_inner_smul_right,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  have hd := direction_value_coupling hN c hc u w (v : Vector N)
  dsimp only [c] at hd
  rw [firstCovariance_center_at,firstCovariance_mixture] at hd
  simpa only [directionObservation,flatJetCLM_apply] using hd

/-- The actual complete tangent-gradient inverse has the literal scalar
precision 1/(Q xi'(Q)); no covariance hypothesis is introduced. -/
theorem center_gradient_inverse_apply {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (u : Vector N) (hu : ‖u‖^2=(N : ℝ))
    (v : tangentPlane u) :
    (gram (intrinsicGamma (centerCoefficients (mixtureCoefficients μ) Q) u)).inverse v=
      (Q*μ.xi1 Q)⁻¹ • v := by
  let A := intrinsicGamma (centerCoefficients (mixtureCoefficients μ) Q) u
  let a := Q*μ.xi1 Q
  have ha : a≠0 := (mul_pos hQ (μ.xi1_pos hQ)).ne'
  have hA := center_intrinsicGamma_surjective hN μ hQ u hu
  have hg := center_intrinsicGamma_gram hN μ hQ.le u hu
  have he := congrArg (fun T => T ((gram A).inverse v)) hg
  have hh : a • (gram A).inverse v=v :=
    he.symm.trans ((gram_isInvertible A hA).self_apply_inverse v)
  calc
    _=a⁻¹ • (a • (gram A).inverse v) := (inv_smul_smul₀ ha _).symm
    _=_ := congrArg (fun t => a⁻¹ • t) hh

/-- Tangent projections retain precisely the overlap component transverse
to the actual center. -/
theorem tangent_value_cross_inner {N : ℕ} (hN : 0 < N)
    (u : Vector N) (hu : ‖u‖^2=(N : ℝ)) (w₁ w₂ : Vector N) :
    inner ℝ ((tangentPlane u).orthogonalProjectionOnto w₁)
      ((tangentPlane u).orthogonalProjectionOnto w₂)=
      (N : ℝ)*(overlap w₁ w₂-overlap u w₁*overlap u w₂) := by
  have hon : OnSphere u := by rw [OnSphere,real_inner_self_eq_norm_sq];exact hu
  have hp : ((tangentPlane u).orthogonalProjectionOnto w₂ : Vector N)=
      tangentProjection u w₂ := by
    change (tangentPlane u).starProjection w₂=tangentProjection u w₂
    rw [tangentProjection_eq_starProjection hN.ne' u hon]
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,hp,
    tangentProjection_apply,projection,inner_sub_right,real_inner_smul_right,
    inner_eq_dimension_overlap hN u w₂,inner_eq_dimension_overlap hN w₁ w₂,
    inner_eq_dimension_overlap hN w₁ u,overlap_comm w₁ u]
  field_simp

private theorem scalar_gradient_adjoint {N P : ℕ}
    (f : EuclideanDisorder N P →L[ℝ] ℝ) (u : Vector N)
    (A : EuclideanDisorder N P →L[ℝ] tangentPlane u) (v : tangentPlane u) :
    f (A.adjoint v)=inner ℝ (A (f.adjoint 1)) v := by
  have h : f (A.adjoint v)=inner ℝ (f.adjoint 1) (A.adjoint v) := by
    rw [f.adjoint_inner_left]
    simp only [RCLike.inner_apply,RCLike.conj_to_real,mul_one]
  rw [h,A.adjoint_inner_right]

/-- The actual tangent-gradient regression contribution to the latitude
covariance, expressed in literal center-overlap polynomial derivatives. -/
theorem center_gradient_regression_cross {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (u : Vector N) (hu : ‖u‖^2=(N : ℝ)) (w₁ w₂ : Vector N) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    valueObservation c w₁ (lift (intrinsicGamma c u)
      (intrinsicGamma c u ((valueObservation c w₂).adjoint 1)))=
      (N : ℝ)*(Q*μ.xi1 (Q*overlap u w₁))*(Q*μ.xi1 (Q*overlap u w₂)) /
        (Q*μ.xi1 Q)*(overlap w₁ w₂-overlap u w₁*overlap u w₂) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  change valueObservation c w₁ ((intrinsicGamma c u).adjoint
    ((gram (intrinsicGamma c u)).inverse
      (intrinsicGamma c u ((valueObservation c w₂).adjoint 1))))=_
  rw [scalar_gradient_adjoint,center_gradient_inverse_apply hN μ hQ u hu,
    center_gradient_value_cross hN μ hQ.le u w₁,center_gradient_value_cross hN μ hQ.le u w₂,
    real_inner_smul_left,real_inner_smul_right,real_inner_smul_right,
    tangent_value_cross_inner hN u hu]
  ring

end
end SlowEquilibration.SphericalCriticalLatitude
