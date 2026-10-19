-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalCriticalLatitudeAuxiliaryLaw

/-! Proper value/zero-gradient whole-field conditioning, with the redundant
radial score omitted. These exact continuous-process and coefficient
projection identities apply to pure mixtures without any inverse Sigma. -/

@[expose] public section
namespace SlowEquilibration.SphericalCriticalLatitude
noncomputable section
open MeasureTheory ProbabilityTheory Function
open SphericalModel SphericalGaussianJet WholeFieldRegression SphericalPosteriorMaps
open SphericalTaylorRemainder SphericalSequentialRegression SphericalMarkedWindows
open GaussianRegression IntrinsicGradientRegression IntrinsicHessianLaw ValueTangentConditioning
open SphericalForm
open scoped RealInnerProductSpace
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def valueCriticalCoefficientResidual (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+1)) : EuclideanDisorder (n+1) μ.maxDegree →L[ℝ]
      EuclideanDisorder (n+1) μ.maxDegree :=
  (gradientResidual n μ Q u).comp (valueResidual n μ Q u)

theorem valueCriticalCoefficientResidual_eq_joint (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ)) :
    valueCriticalCoefficientResidual n μ Q u=
      residual (valueTangentCLM (centerCoefficients (mixtureCoefficients μ) Q) u (tangentFrame u hu)) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hc := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  rw [valueCriticalCoefficientResidual,gradientResidual_eq n μ hQ u hu,
    valueResidual_eq n μ hQ.le u hu]
  exact (orthogonal_joint_residual (intrinsicGamma c u) (valueCLM c u)
    (valueTangentCLM c u (tangentFrame u hu))
    (center_intrinsicGamma_surjective (by omega) μ hQ u hu)
    (center_value_surjective μ hQ u hu)
    (center_valueTangent_surjective (by omega) μ hQ u hu _
      (tangentFrame_orthonormal u hu) (tangentFrame_tangent u hu))
    (orthogonal_observation_symm _ _ (value_intrinsic_adjoint_zero c hc u))
    (valueTangentCLM_ker_intrinsic_value c u hu)).symm

theorem valueCriticalCoefficientResidual_projection (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ)) :
    (valueCriticalCoefficientResidual n μ Q u).adjoint=valueCriticalCoefficientResidual n μ Q u ∧
    (valueCriticalCoefficientResidual n μ Q u).comp (valueCriticalCoefficientResidual n μ Q u)=
      valueCriticalCoefficientResidual n μ Q u := by
  rw [valueCriticalCoefficientResidual_eq_joint n μ hQ u hu]
  have hC := center_valueTangent_surjective (by omega) μ hQ u hu _
    (tangentFrame_orthonormal u hu) (tangentFrame_tangent u hu)
  exact ⟨residual_adjoint _ hC,residual_comp_self _ hC⟩

theorem value_critical_residual_scalar_kernel (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (f g : EuclideanDisorder (n+1) μ.maxDegree →L[ℝ] ℝ) :
    (f.comp (valueCriticalCoefficientResidual n μ Q u))
      ((g.comp (valueCriticalCoefficientResidual n μ Q u)).adjoint 1)=
      f (valueCriticalCoefficientResidual n μ Q u (g.adjoint 1)) := by
  obtain ⟨hAdj,hIdem⟩ := valueCriticalCoefficientResidual_projection n μ hQ u hu
  simp only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.comp_apply,hAdj]
  exact congrArg f (congrArg (fun L => L (g.adjoint 1)) hIdem)

theorem value_critical_residual_split (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (g : EuclideanDisorder (n+1) μ.maxDegree) :
    valueCriticalCoefficientResidual n μ Q u g=
      g-lift (valueCLM (centerCoefficients (mixtureCoefficients μ) Q) u)
        (valueCLM (centerCoefficients (mixtureCoefficients μ) Q) u g)-
      lift (intrinsicGamma (centerCoefficients (mixtureCoefficients μ) Q) u)
        (intrinsicGamma (centerCoefficients (mixtureCoefficients μ) Q) u g) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hc := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hGV := orthogonal_observation_symm _ _ (value_intrinsic_adjoint_zero c hc u)
  rw [valueCriticalCoefficientResidual,ContinuousLinearMap.comp_apply,
    gradientResidual_eq n μ hQ u hu,valueResidual_eq n μ hQ.le u hu]
  change g-lift (valueCLM c u) (valueCLM c u g)-
    lift (intrinsicGamma c u) (intrinsicGamma c u (g-lift (valueCLM c u) (valueCLM c u g)))=_
  rw [map_sub,orthogonal_observation_lift_zero _ _ hGV,sub_zero]

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

def valueCriticalContinuousMean (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+1)) (z : K → Vector (n+1)) (hz : Continuous z) (e : ℝ) : C(K,ℝ) :=
  criticalContinuousField n μ Q z hz (valueLift n μ Q u ((n+1 : ℕ)*e))

def valueCriticalContinuousResidual (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+1)) (z : K → Vector (n+1)) (hz : Continuous z) :
    EuclideanDisorder (n+1) μ.maxDegree →L[ℝ] C(K,ℝ) :=
  (criticalContinuousField n μ Q z hz).comp (valueCriticalCoefficientResidual n μ Q u)

omit [CompactSpace K] in
theorem valueCriticalContinuousField_posterior (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+1)) (z : K → Vector (n+1)) (hz : Continuous z) (e : ℝ)
    (g : EuclideanDisorder (n+1) μ.maxDegree) :
    criticalContinuousField n μ Q z hz (valuePosterior n μ Q u e g)=
      valueCriticalContinuousResidual n μ Q u z hz g+valueCriticalContinuousMean n μ Q u z hz e := by
  simp only [valueCriticalContinuousResidual,valueCriticalContinuousMean,valuePosterior,
    valueCriticalCoefficientResidual,ContinuousLinearMap.comp_apply,map_add]

/-- Exact proper scalar-value conditional law, including pure models and
every prescribed energy, as the same true Gaussian continuous residual. -/
theorem actual_value_critical_centered_continuous_law
    [SecondCountableTopology K] [T2Space K] [Nonempty K]
    (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (z : K → Vector (n+1)) (hz : Continuous z) (e : ℝ) :
    (valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu e).map
      (fun J => criticalContinuousField n μ Q z hz (euclideanDisorder J)-
        valueCriticalContinuousMean n μ Q u z hz e)=
      (stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)).map
        (valueCriticalContinuousResidual n μ Q u z hz) := by
  have hm : Measurable (fun J : Disorder (n+1) μ.maxDegree =>
      criticalContinuousField n μ Q z hz (euclideanDisorder J)-
        valueCriticalContinuousMean n μ Q u z hz e) :=
    ((criticalContinuousField n μ Q z hz).continuous.measurable.comp
      (SphericalTaylorRemainder.euclideanDisorder_measurable _ _)).sub measurable_const
  have hp : Continuous (fun g => valuePosterior n μ Q u e g) := by
    unfold valuePosterior
    exact ((gradientResidual n μ Q u).continuous.comp
      (valueResidual n μ Q u).continuous).add continuous_const
  have hp' : Measurable (fun g : EuclideanDisorder (n+1) μ.maxDegree =>
      unpackCLM (n+1) μ.maxDegree (valuePosterior n μ Q u e g)) :=
    (unpackCLM (n+1) μ.maxDegree).continuous.measurable.comp hp.measurable
  rw [valueConditionedLaw_eq_map n μ hQ u hu e,Measure.map_map hm hp']
  congr 1
  funext g
  change criticalContinuousField n μ Q z hz (valuePosterior n μ Q u e g)-
    valueCriticalContinuousMean n μ Q u z hz e=valueCriticalContinuousResidual n μ Q u z hz g
  rw [valueCriticalContinuousField_posterior,add_sub_cancel_right]

end
end SlowEquilibration.SphericalCriticalLatitude
