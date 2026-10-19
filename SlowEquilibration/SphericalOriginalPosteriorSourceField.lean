-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalOriginalCenterLift

/-! Literal original-field affine realization of the actual center-score
and proper value/zero-gradient posteriors. The center and original fields
are distinguished throughout; their cross is evaluated at sqrt(Q) r. -/

@[expose] public section
namespace SlowEquilibration.ConditionedEntrance
noncomputable section
open SphericalModel SphericalGaussianJet SphericalForm SphericalMarkedWindows

/-- The proper value-and-zero-gradient source correction. It uses the
nonredundant scalar value observation, also for a proper pure mixture. -/
def sourceValueRegressionCorrection {N : ℕ} (μ : FiniteMixture) (Q : ℝ)
    (J : Disorder N μ.maxDegree) (u : Vector N) (e : ℝ) (x : Vector N) : ℝ :=
  let c := centerCoefficients (mixtureCoefficients μ) Q
  μ.xi (Real.sqrt Q*overlap x u)/μ.xi Q*((N : ℝ)*e-field c J u)-
    tangentTheta μ Q (overlap x u)*inner ℝ (surfaceGradient (field c J) u) x

end
end SlowEquilibration.ConditionedEntrance

namespace SlowEquilibration.SphericalCriticalLatitude
noncomputable section
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet WholeFieldRegression SphericalTaylorRemainder
open SphericalMarkedWindows SphericalPosteriorMaps IntrinsicGradientRegression SphericalForm
open GaussianRegression SphericalSequentialRegression ConditionedEntrance
open scoped RealInnerProductSpace BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem center_gradient_scoreResidual (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0<Q) (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (g : EuclideanDisorder (n+1) μ.maxDegree) :
    intrinsicGamma (centerCoefficients (mixtureCoefficients μ) Q) u
      (scoreResidual n μ Q u g)=
      intrinsicGamma (centerCoefficients (mixtureCoefficients μ) Q) u g := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hc := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  rw [scoreResidual,sub_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply,
    map_sub,scoreLift_eq n μ hQ.le u hu,
    orthogonal_observation_lift_zero _ _
      (orthogonal_observation_symm _ _ (score_intrinsic_adjoint_zero c hc u)),sub_zero]

private theorem center_gradient_valueResidual (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0<Q) (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (g : EuclideanDisorder (n+1) μ.maxDegree) :
    intrinsicGamma (centerCoefficients (mixtureCoefficients μ) Q) u
      (valueResidual n μ Q u g)=
      intrinsicGamma (centerCoefficients (mixtureCoefficients μ) Q) u g := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hc := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  rw [valueResidual,sub_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply,
    map_sub,valueLift_eq n μ hQ.le u hu,
    orthogonal_observation_lift_zero _ _
      (orthogonal_observation_symm _ _ (value_intrinsic_adjoint_zero c hc u)),sub_zero]

/-- Every original coefficient seed, every physical axis and every score
mark give the literal source field H plus the manuscript correction. -/
theorem actual_mixedPosterior_original_field (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0<Q) (hnp : μ.minDegree<μ.maxDegree)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (e k : ℝ)
    (g : EuclideanDisorder (n+1) μ.maxDegree) (x : Vector (n+1)) :
    fieldOfMixture μ (unpackDisorder (mixedPosterior n μ Q u (scorePairEquiv (e,k)) g)) x=
      fieldOfMixture μ (unpackDisorder g) x+
        sourceRegressionCorrection μ Q hQ hnp (unpackDisorder g) u e k x := by
  have hf (v : EuclideanDisorder (n+1) μ.maxDegree) :
      valueObservation (mixtureCoefficients μ) x v=field (mixtureCoefficients μ) (unpackDisorder v) x := by
    simp only [valueObservation,flatJetCLM_apply,jet,iteratedFDeriv_zero_apply]
  simp only [fieldOfMixture]
  rw [←hf]
  rw [mixedPosterior,gradientResidual_eq n μ hQ u hu]
  simp only [GaussianRegression.residual,sub_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply,
    map_add,map_sub]
  rw [center_gradient_scoreResidual n μ hQ u hu]
  rw [original_gradient_lift_apply (by omega) μ hQ u hu]
  rw [scoreResidual,sub_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply,map_sub,
    original_scoreLift_apply n μ hQ hnp u hu]
  rw [scoreLift_eq n μ hQ.le u hu,original_value_physical_score_lift (by omega) μ hQ hnp u hu]
  rw [intrinsicGamma_coe (by omega) _ u hu]
  simp only [sourceRegressionCorrection,regressionCorrection,
    valueObservation,flatJetCLM_apply,jet,iteratedFDeriv_zero_apply,
    scoreCLM_apply_zero,scoreCLM_apply_one]
  ring

/-- The proper value posterior has the genuine scalar-value correction.
No two-dimensional score covariance is used in this identity. -/
theorem actual_valuePosterior_original_field (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0<Q) (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (e : ℝ)
    (g : EuclideanDisorder (n+1) μ.maxDegree) (x : Vector (n+1)) :
    fieldOfMixture μ (unpackDisorder (valuePosterior n μ Q u e g)) x=
      fieldOfMixture μ (unpackDisorder g) x+
        sourceValueRegressionCorrection μ Q (unpackDisorder g) u e x := by
  have hf (v : EuclideanDisorder (n+1) μ.maxDegree) :
      valueObservation (mixtureCoefficients μ) x v=field (mixtureCoefficients μ) (unpackDisorder v) x := by
    simp only [valueObservation,flatJetCLM_apply,jet,iteratedFDeriv_zero_apply]
  simp only [fieldOfMixture]
  rw [←hf]
  rw [valuePosterior,gradientResidual_eq n μ hQ u hu]
  simp only [GaussianRegression.residual,sub_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply,
    map_add,map_sub]
  rw [center_gradient_valueResidual n μ hQ u hu]
  rw [original_gradient_lift_apply (by omega) μ hQ u hu]
  rw [valueResidual,sub_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply,map_sub,
    original_valueLift_apply n μ hQ u hu,original_valueLift_apply n μ hQ u hu]
  rw [intrinsicGamma_coe (by omega) _ u hu]
  simp only [sourceValueRegressionCorrection,valueObservation,
    SphericalSequentialRegression.valueCLM,flatJetCLM_apply,jet,iteratedFDeriv_zero_apply]
  ring

end
end SlowEquilibration.SphericalCriticalLatitude
