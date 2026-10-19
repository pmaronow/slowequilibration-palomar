-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalCriticalLatitudeContinuousLaw
public import SlowEquilibration.GaussianRegressionSchur

/-! The literal coefficient residual of the actual mixed critical-point
posterior is the joint orthogonal kernel projection. Its evaluation covariance
is derived by subtracting the true score and tangent-gradient regressions. -/

@[expose] public section
namespace SlowEquilibration.SphericalCriticalLatitude
noncomputable section
open MeasureTheory ProbabilityTheory Function
open SphericalModel SphericalGaussianJet WholeFieldRegression SphericalPosteriorMaps
open SphericalTaylorRemainder SphericalSequentialRegression SphericalMarkedWindows
open SphericalTwoPointCovariance GaussianRegression IntrinsicGradientRegression
open IntrinsicHessianLaw SphericalForm
open GaussianContinuousFieldLaw
open scoped RealInnerProductSpace
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def criticalCoefficientResidual (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+1)) : EuclideanDisorder (n+1) μ.maxDegree →L[ℝ]
      EuclideanDisorder (n+1) μ.maxDegree :=
  (gradientResidual n μ Q u).comp (scoreResidual n μ Q u)

/-- The actual two sequential residual maps are exactly the joint
orthogonal projection for the literal value/radial/tangent observation. -/
theorem criticalCoefficientResidual_eq_joint (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ)) :
    criticalCoefficientResidual n μ Q u=
      residual (jointCLM (centerCoefficients (mixtureCoefficients μ) Q) u (tangentFrame u hu)) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hc := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  rw [criticalCoefficientResidual,gradientResidual_eq n μ hQ u hu,
    scoreResidual_eq n μ hQ.le u hu]
  exact (orthogonal_joint_residual (intrinsicGamma c u) (scoreCLM c u)
    (jointCLM c u (tangentFrame u hu))
    (center_intrinsicGamma_surjective (by omega) μ hQ u hu)
    (center_score_surjective (by omega) μ hQ hnp u hu)
    (center_joint_surjective (by omega) μ hQ hnp u hu _
      (tangentFrame_orthonormal u hu) (tangentFrame_tangent u hu))
    (orthogonal_observation_symm _ _ (score_intrinsic_adjoint_zero c hc u))
    (jointCLM_ker_intrinsic_score c u hu)).symm

/-- The true conditional coefficient covariance is an idempotent
self-adjoint projection, at every actual sphere point. -/
theorem criticalCoefficientResidual_projection (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ)) :
    (criticalCoefficientResidual n μ Q u).adjoint=criticalCoefficientResidual n μ Q u ∧
    (criticalCoefficientResidual n μ Q u).comp (criticalCoefficientResidual n μ Q u)=
      criticalCoefficientResidual n μ Q u := by
  rw [criticalCoefficientResidual_eq_joint n μ hQ hnp u hu]
  have hC := center_joint_surjective (by omega) μ hQ hnp u hu _
    (tangentFrame_orthonormal u hu) (tangentFrame_tangent u hu)
  exact ⟨residual_adjoint _ hC,residual_comp_self _ hC⟩

/-- Exact value of every scalar cross covariance of the true residual
coefficient process. -/
theorem critical_residual_scalar_kernel (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (f g : EuclideanDisorder (n+1) μ.maxDegree →L[ℝ] ℝ) :
    (f.comp (criticalCoefficientResidual n μ Q u))
      ((g.comp (criticalCoefficientResidual n μ Q u)).adjoint 1)=
      f (criticalCoefficientResidual n μ Q u (g.adjoint 1)) := by
  obtain ⟨hAdj,hIdem⟩ := criticalCoefficientResidual_projection n μ hQ hnp u hu
  simp only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.comp_apply,hAdj]
  exact congrArg f (congrArg (fun L => L (g.adjoint 1)) hIdem)

/-- The actual residual removes precisely the score and tangent-gradient
regressions. Their orthogonality is proved for the real tensor observations. -/
theorem critical_residual_split (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (g : EuclideanDisorder (n+1) μ.maxDegree) :
    criticalCoefficientResidual n μ Q u g=
      g-lift (scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) u)
        (scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) u g)-
      lift (intrinsicGamma (centerCoefficients (mixtureCoefficients μ) Q) u)
        (intrinsicGamma (centerCoefficients (mixtureCoefficients μ) Q) u g) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hc := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hGS := orthogonal_observation_symm _ _ (score_intrinsic_adjoint_zero c hc u)
  rw [criticalCoefficientResidual,ContinuousLinearMap.comp_apply,
    gradientResidual_eq n μ hQ u hu,scoreResidual_eq n μ hQ.le u hu]
  change g-lift (scoreCLM c u) (scoreCLM c u g)-
    lift (intrinsicGamma c u) (intrinsicGamma c u (g-lift (scoreCLM c u) (scoreCLM c u g)))=_
  rw [map_sub,orthogonal_observation_lift_zero _ _ hGS,sub_zero]

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

omit [CompactSpace K] in
/-- Exact evaluation covariance of the actual centered continuous field,
before simplifying its genuine score/gradient contractions to tau_r. -/
theorem criticalContinuousResidual_covariance (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (z : K → Vector (n+1)) (hz : Continuous z) (v w : K) :
    cov[fun g => criticalContinuousResidual n μ Q u z hz g v,
      fun g => criticalContinuousResidual n μ Q u z hz g w;
        stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)]=
      valueObservation (centerCoefficients (mixtureCoefficients μ) Q) (z v)
        (criticalCoefficientResidual n μ Q u
          ((valueObservation (centerCoefficients (mixtureCoefficients μ) Q) (z w)).adjoint 1)) := by
  rw [evaluation_covariance]
  change (valueObservation (centerCoefficients (mixtureCoefficients μ) Q) (z v)).comp
    (criticalCoefficientResidual n μ Q u)
      (((valueObservation (centerCoefficients (mixtureCoefficients μ) Q) (z w)).comp
        (criticalCoefficientResidual n μ Q u)).adjoint 1)=_
  exact critical_residual_scalar_kernel n μ hQ hnp u hu _ _

end
end SlowEquilibration.SphericalCriticalLatitude
