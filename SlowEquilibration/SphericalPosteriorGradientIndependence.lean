-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalOriginalPosteriorSourceField
public import SlowEquilibration.SphericalDisorderPathKernel

/-! The actual full original posterior coefficients are independent of the
original center tangent gradient, on the same literal Gaussian bank. -/
@[expose] public section
namespace SlowEquilibration.SphericalPosteriorGradientIndependence
noncomputable section
open Function MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalForm SphericalGaussianJet WholeFieldRegression
open GaussianRegression IntrinsicGradientRegression SphericalSequentialRegression SphericalPosteriorMaps
open scoped Topology ENNReal RealInnerProductSpace
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000

theorem orthogonal_residual_commute {E F G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    (A : E→L[ℝ]F) (B : E→L[ℝ]G) (hAB : A.comp B.adjoint=0) :
    (residual A).comp (residual B)=(residual B).comp (residual A) := by
  have hBA := orthogonal_observation_symm A B hAB
  apply ContinuousLinearMap.ext
  intro z
  change residual B z-lift A (A (residual B z))=residual A z-lift B (B (residual A z))
  have hA : A (residual B z)=A z := by
    change A (z-lift B (B z))=A z
    rw [map_sub,orthogonal_observation_lift_zero A B hAB,sub_zero]
  have hB : B (residual A z)=B z := by
    change B (z-lift A (A z))=B z
    rw [map_sub,orthogonal_observation_lift_zero B A hBA,sub_zero]
  rw [hA,hB]
  change (z-lift B (B z))-lift A (A z)=(z-lift A (A z))-lift B (B z)
  abel

theorem mixedPosterior_independent_original_gradient (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (u : Vector (n+1)) (hu : ‖u‖^2=(n+1:ℕ))
    (marks : EuclideanSpace ℝ (Fin 2)) :
    IndepFun (mixedPosterior n μ Q u marks)
      (fun g : EuclideanDisorder (n+1) μ.maxDegree=>
        surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder g)) u)
      (stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let A := intrinsicGamma c u
  let B := scoreCLM c u
  have hc : ∀ p,0 ≤ c p := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hA := center_intrinsicGamma_surjective (by omega : 0 < n+1) μ hQ u hu
  have hAB := orthogonal_observation_symm B A (score_intrinsic_adjoint_zero c hc u)
  have hComm := orthogonal_residual_commute A B hAB
  let f := fun z : EuclideanDisorder (n+1) μ.maxDegree=>
    residual B z+scoreLift n μ Q u (((n+1:ℕ):ℝ) • marks)
  have hf : Measurable f := (residual B).continuous.measurable.add_const _
  have hh := (residual_observation_independent A hA).comp hf
    (measurable_subtype_coe : Measurable (fun z : tangentPlane u=>(z:Vector (n+1))))
  have hleft : f ∘ residual A=mixedPosterior n μ Q u marks := by
    funext g
    rw [mixedPosterior,gradientResidual_eq n μ hQ u hu,scoreResidual_eq n μ hQ.le u hu]
    have he := congrArg (fun L=>L g) hComm
    simp only [ContinuousLinearMap.comp_apply] at he
    exact congrArg (fun z=>z+scoreLift n μ Q u (((n+1:ℕ):ℝ) • marks)) he.symm
  have hright : (fun z : tangentPlane u=>(z:Vector (n+1))) ∘ A =
      (fun g=>surfaceGradient (field c (unpackDisorder g)) u) := by
    funext g
    exact intrinsicGamma_coe (by omega : n+1≠0) c u hu g
  rw [hleft,hright] at hh
  exact hh

theorem valuePosterior_independent_original_gradient (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (u : Vector (n+1)) (hu : ‖u‖^2=(n+1:ℕ)) (mark : ℝ) :
    IndepFun (valuePosterior n μ Q u mark)
      (fun g : EuclideanDisorder (n+1) μ.maxDegree=>
        surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder g)) u)
      (stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let A := intrinsicGamma c u
  let B := valueCLM c u
  have hc : ∀ p,0 ≤ c p := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hA := center_intrinsicGamma_surjective (by omega : 0 < n+1) μ hQ u hu
  have hAB := orthogonal_observation_symm B A (value_intrinsic_adjoint_zero c hc u)
  have hComm := orthogonal_residual_commute A B hAB
  let f := fun z : EuclideanDisorder (n+1) μ.maxDegree=>
    residual B z+valueLift n μ Q u ((n+1:ℕ)*mark)
  have hf : Measurable f := (residual B).continuous.measurable.add_const _
  have hh := (residual_observation_independent A hA).comp hf
    (measurable_subtype_coe : Measurable (fun z : tangentPlane u=>(z:Vector (n+1))))
  have hleft : f ∘ residual A=valuePosterior n μ Q u mark := by
    funext g
    rw [valuePosterior,gradientResidual_eq n μ hQ u hu,valueResidual_eq n μ hQ.le u hu]
    have he := congrArg (fun L=>L g) hComm
    simp only [ContinuousLinearMap.comp_apply] at he
    exact congrArg (fun z=>z+valueLift n μ Q u ((n+1:ℕ)*mark)) he.symm
  have hright : (fun z : tangentPlane u=>(z:Vector (n+1))) ∘ A =
      (fun g=>surfaceGradient (field c (unpackDisorder g)) u) := by
    funext g
    exact intrinsicGamma_coe (by omega : n+1≠0) c u hu g
  rw [hleft,hright] at hh
  exact hh

end
end SlowEquilibration.SphericalPosteriorGradientIndependence
