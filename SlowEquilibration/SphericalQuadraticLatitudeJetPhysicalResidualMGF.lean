-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianOrthogonalScalarResidualVariance
public import SlowEquilibration.GaussianCoefficientKernelScalarExpIntegrable

@[expose] public section

/-! The genuine nonquadratic latitude field has the manuscript's residual
Gaussian variance after the true mixed score/gradient conditioning. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory ProbabilityTheory Function SphericalModel SphericalGaussianJet
open WholeFieldRegression GaussianRegression IntrinsicHessianLaw
open SphericalSequentialRegression SphericalTaylorRemainder
open SphericalTAPMixedBandExponent SphericalTAPCriticalAnalyticNeighborhood
open ConditionedDeterminantMoments
open GaussianOrthogonalScalarResidualVariance
open GaussianCoefficientKernelScalarMGF
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem scalarCLM_norm_sq_eq {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E →L[ℝ] ℝ) : ‖f‖^2=f (f.adjoint 1) := by
  have hf : f=innerSL ℝ (f.adjoint 1) := by
    ext x
    have hh : f x=inner ℝ (f.adjoint 1) x := by
      rw [f.adjoint_inner_left]
      simp
    simpa only [innerSL_apply_apply] using hh
  rw [hf,innerSL_apply_norm,ContinuousLinearMap.adjoint_innerSL_apply]
  simp [innerSL_apply_apply]

theorem flatNonquadraticLatitudeField_physicalResidual_variance
    {n : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (a : ℝ) (ha : 0 ≤ 1-a^2) (u ω : Vector (n+2))
    (hu : ‖u‖^2=((n+2:ℕ):ℝ))
    (hω : inner ℝ ω u=0)
    (hωn : ‖ω‖^2=((n+2:ℕ):ℝ)) :
    let A := jointCLM (centerCoefficients (mixtureCoefficients μ) Q)
      u (tangentFrame u hu)
    ‖(flatNonquadraticLatitudeField μ a u ω).comp (residual A)‖^2 =
      ((n+2:ℕ):ℝ)*(sourceMixedVariance μ Q a-
        sourceQuadraticLatitudeVariance μ a) := by
  dsimp only
  let A := jointCLM (centerCoefficients (mixtureCoefficients μ) Q)
      u (tangentFrame u hu)
  let f := valueObservation (mixtureCoefficients μ)
    (originalLatitudePoint a u ω)
  let y := flatQuadraticLatitudeJet μ a u ω
  have hA : Surjective A :=
    center_joint_surjective (by omega) μ hQ hnp u hu _
      (tangentFrame_orthonormal u hu) (tangentFrame_tangent u hu)
  have hyA : y.comp A.adjoint=0 :=
    flatQuadraticLatitudeJet_physicalJoint_cross_zero
      (by omega : 0 < n+2) μ hμ Q a u ω hω (tangentFrame u hu)
  have hyf : y (f.adjoint 1)=y (y.adjoint 1) := by
    rw [← scalar_observation_covariance y f,
      ← scalar_observation_covariance y y]
    simp only [y,f,flatQuadraticLatitudeJet_actual,valueObservation_actual]
    change cov[quadraticLatitudeJet μ a u ω,
      fun J => field (mixtureCoefficients μ) J
        (originalLatitudePoint a u ω);disorderLaw (n+2) μ.maxDegree] =
      cov[quadraticLatitudeJet μ a u ω,
        quadraticLatitudeJet μ a u ω;disorderLaw (n+2) μ.maxDegree]
    rw [quadraticLatitudeJet_originalLatitudeField_covariance
      (by omega) μ a ha u ω ω hu hω hω,
      quadraticLatitudeJet_covariance
        (by omega) μ a u ω ω hu hω hω]
  have hyNorm : ‖y‖^2 =
      ((n+2:ℕ):ℝ)*sourceQuadraticLatitudeVariance μ a := by
    rw [scalarCLM_norm_sq_eq,
      ← scalar_observation_covariance y y]
    simp only [y,flatQuadraticLatitudeJet_actual]
    change cov[quadraticLatitudeJet μ a u ω,
      quadraticLatitudeJet μ a u ω;disorderLaw (n+2) μ.maxDegree] = _
    rw [quadraticLatitudeJet_covariance
      (by omega) μ a u ω ω hu hω hω,
      overlap_self (by omega) ω hωn]
    ring
  have hF := originalLatitudePoint_originalField_residualGram
    μ hQ hnp a ha u ω hu hω hωn
  have hSub := scalar_residual_bank_subtraction A hA f y hyA hyf
  change ‖(flatNonquadraticLatitudeField μ a u ω).comp (residual A)‖^2 = _ at hSub
  rw [hF,hyNorm] at hSub
  convert hSub using 1
  ring

/-- The scalar exponential factor in printed `mb-quadratic`, with the
actual original tensor field and every literal mixed Palm mark. -/
theorem nonquadraticLatitudeField_physicalMixedPalm_exp_integral
    {n : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (a β : ℝ) (ha : 0 ≤ 1-a^2) (u ω : Vector (n+2))
    (hu : ‖u‖^2=((n+2:ℕ):ℝ))
    (hω : inner ℝ ω u=0)
    (hωn : ‖ω‖^2=((n+2:ℕ):ℝ))
    (z : EuclideanSpace ℝ (Fin 2)) :
    (∫ J, Real.exp (β*(field (mixtureCoefficients μ) J
        (originalLatitudePoint a u ω)-quadraticLatitudeJet μ a u ω J))
      ∂mixedLaw μ Q u hu z) =
      Real.exp (((n+2:ℕ):ℝ)*
        (β*sourceMixedMean μ Q (z 0) (z 1) a+
          β^2/2*(sourceMixedVariance μ Q a-
            sourceQuadraticLatitudeVariance μ a))) := by
  let A := jointCLM (centerCoefficients (mixtureCoefficients μ) Q)
    u (tangentFrame u hu)
  let B := flatNonquadraticLatitudeField μ a u ω
  let w := jointScoreTarget (n+1) (((n+2:ℕ):ℝ) • z)
  have h := coefficientKernel_scalar_exp_integral A B w β
  have hm := flatNonquadraticLatitudeField_physicalMixedPalm_mean
    μ hμ hQ hnp a u ω hu hω z
  have hv := flatNonquadraticLatitudeField_physicalResidual_variance
    μ hμ hQ hnp a ha u ω hu hω hωn
  change B (lift A w) = _ at hm
  change ‖B.comp (residual A)‖^2 = _ at hv
  rw [hm,hv] at h
  change (∫ J,Real.exp (β*actualObservation B J)
    ∂coefficientKernel A w) = _ at h
  convert h using 1
  · apply integral_congr_ae
    filter_upwards with J
    rw [show actualObservation B J =
      field (mixtureCoefficients μ) J (originalLatitudePoint a u ω)-
        quadraticLatitudeJet μ a u ω J from
      flatNonquadraticLatitudeField_actual μ a u ω J]
  · congr 1
    ring

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
