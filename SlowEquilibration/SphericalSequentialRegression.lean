-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianOrthogonalRegression
public import SlowEquilibration.ValueTangentConditioning

/-! Full-field disintegration at the actual specified zero tangent gradient.
The score conditioning retains every original tensor coefficient. -/

@[expose] public section

namespace SlowEquilibration.SphericalSequentialRegression

open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression SlowEquilibration.IntrinsicGradientRegression
open SlowEquilibration.IntrinsicHessianLaw SlowEquilibration.GaussianRegression
open SlowEquilibration.ValueTangentConditioning SlowEquilibration.SphericalForm
open scoped ENNReal Topology RealInnerProductSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem coefficientKernel_orthogonal_zero_disintegration {N P : ℕ} {F G H : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    (A : EuclideanDisorder N P →L[ℝ] F) (B : EuclideanDisorder N P →L[ℝ] G)
    (C : EuclideanDisorder N P →L[ℝ] H)
    (hA : Surjective A) (hB : Surjective B) (hC : Surjective C)
    (hAB : A.comp B.adjoint = 0) (hker : C.ker = A.ker ⊓ B.ker)
    (phi : Disorder N P → ℝ≥0∞) (hphi : Measurable phi) :
    (∫⁻ J, phi J ∂coefficientKernel A 0) =
      ∫⁻ b, ∫⁻ J, phi J ∂coefficientKernel C (C (lift B b)) ∂observationLaw B := by
  have h := orthogonal_zero_disintegration A B C hA hB hC hAB hker
    (fun g => phi (unpackCLM N P g)) (hphi.comp (unpackCLM N P).continuous.measurable)
  rw [coefficientKernel_apply, lintegral_map hphi (unpackCLM N P).continuous.measurable, h]
  apply lintegral_congr
  intro b
  rw [coefficientKernel_apply, lintegral_map hphi (unpackCLM N P).continuous.measurable]

/-- Actual value and radial observations are orthogonal to the complete
intrinsic gradient, by the field's actual Gaussian jet covariances. -/
theorem score_intrinsic_adjoint_zero {N P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (x : Vector N) :
    (scoreCLM c x).comp (intrinsicGamma c x).adjoint = 0 := by
  apply ContinuousLinearMap.ext
  intro w
  apply PiLp.ext
  intro i
  have h := actual_scalar_cross_covariance ((EuclideanSpace.proj i).comp (scoreCLM c x))
    (intrinsicGamma c x) w
  simp only [ContinuousLinearMap.comp_apply, EuclideanSpace.coe_proj,
    intrinsicGamma_inner, unpack_euclideanDisorder] at h
  change scoreCLM c x ((intrinsicGamma c x).adjoint w) i = 0
  rw [← h]
  have hw : inner ℝ (w : Vector N) x = 0 := by
    rw [real_inner_comm]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.2
  fin_cases i
  · change cov[fun J : Disorder N P => scoreCLM c x (euclideanDisorder J) 0,
      fun J => jet c 1 x (fun _ => (w : Vector N)) J; disorderLaw N P] = 0
    simpa only [scoreCLM_apply_zero, unpack_euclideanDisorder] using
      value_tangent_gradient_covariance_zero c hc x w hw
  · change cov[fun J : Disorder N P => scoreCLM c x (euclideanDisorder J) 1,
      fun J => jet c 1 x (fun _ => (w : Vector N)) J; disorderLaw N P] = 0
    simpa only [scoreCLM_apply_one, unpack_euclideanDisorder] using
      radial_tangent_gradient_covariance_zero c hc x w hw

/-- Coordinates in the constructed complete tangent basis represent exactly
the intrinsic gradient, including its full zero predicate. -/
theorem tangentFrame_gradient_eq {n P : ℕ} (c : Degree P → ℝ)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ)) (g : EuclideanDisorder (n+1) P) :
    gradientCLM c x (tangentFrame x hx) g = (tangentBasis x hx).repr (intrinsicGamma c x g) := by
  apply PiLp.ext
  intro i
  rw [OrthonormalBasis.repr_apply_apply, intrinsicGamma_inner, gradientCLM_apply]
  rfl

theorem tangentFrame_gradient_zero_iff {n P : ℕ} (c : Degree P → ℝ)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ)) (g : EuclideanDisorder (n+1) P) :
    gradientCLM c x (tangentFrame x hx) g = 0 ↔ intrinsicGamma c x g = 0 := by
  rw [tangentFrame_gradient_eq]
  exact (tangentBasis x hx).repr.map_eq_zero_iff

theorem jointCLM_ker_intrinsic_score {n P : ℕ} (c : Degree P → ℝ)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ)) :
    (jointCLM c x (tangentFrame x hx)).ker = (intrinsicGamma c x).ker ⊓ (scoreCLM c x).ker := by
  ext g
  change jointCLM c x (tangentFrame x hx) g = 0 ↔
    intrinsicGamma c x g = 0 ∧ scoreCLM c x g = 0
  rw [← tangentFrame_gradient_zero_iff c x hx g]
  constructor
  · intro h
    constructor
    · apply PiLp.ext
      intro i
      have hi := congrArg (fun v => v (Sum.inr i)) h
      simpa only [jointCLM_apply_inr, PiLp.zero_apply] using hi
    · apply PiLp.ext
      intro i
      have hi := congrArg (fun v => v (Sum.inl i)) h
      simpa only [jointCLM_apply_inl, PiLp.zero_apply] using hi
  · rintro ⟨hg, hs⟩
    apply PiLp.ext
    intro i
    cases i <;> simp [hg, hs]

/-- Literal unnormalized value/radial target together with tangent gradient zero. -/
def jointScoreTarget (n : ℕ) (b : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Sum (Fin 2) (Fin n)) :=
  WithLp.toLp 2 (Sum.elim (fun i => b i) (fun _ => 0))

theorem jointCLM_score_lift {n P : ℕ} (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ))
    (hscore : Surjective (scoreCLM c x)) (b : EuclideanSpace ℝ (Fin 2)) :
    jointCLM c x (tangentFrame x hx) (lift (scoreCLM c x) b) = jointScoreTarget n b := by
  apply PiLp.ext
  intro i
  cases i with
  | inl i =>
    change scoreCLM c x (lift (scoreCLM c x) b) i = b i
    rw [observation_lift_apply _ hscore]
  | inr i =>
    change gradientCLM c x (tangentFrame x hx) (lift (scoreCLM c x) b) i = 0
    rw [tangentFrame_gradient_eq, orthogonal_observation_lift_zero _ _
      (orthogonal_observation_symm _ _ (score_intrinsic_adjoint_zero c hc x)), map_zero]
    rfl

/-- Nonpure conditioned-law disintegration for arbitrary Borel functions of
the entire original tensor field, at the literal intrinsic-gradient zero. -/
theorem intrinsic_zero_score_disintegration {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ))
    (phi : Disorder (n+1) μ.maxDegree → ℝ≥0∞) (hphi : Measurable phi) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, phi J ∂coefficientKernel (intrinsicGamma c x) 0) =
      ∫⁻ b, ∫⁻ J, phi J ∂coefficientKernel (jointCLM c x (tangentFrame x hx))
        (jointScoreTarget n b) ∂observationLaw (scoreCLM c x) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hc := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hscore := center_score_surjective (by omega) μ hQ hnp x hx
  have h := coefficientKernel_orthogonal_zero_disintegration
    (intrinsicGamma c x) (scoreCLM c x) (jointCLM c x (tangentFrame x hx))
    (center_intrinsicGamma_surjective (by omega) μ hQ x hx) hscore
    (center_joint_surjective (by omega) μ hQ hnp x hx _
      (tangentFrame_orthonormal x hx) (tangentFrame_tangent x hx))
    (orthogonal_observation_symm _ _ (score_intrinsic_adjoint_zero c hc x))
    (jointCLM_ker_intrinsic_score c x hx) phi hphi
  simpa only [jointCLM_score_lift c hc x hx hscore] using h

/-- Actual scalar value observation, without a redundant radial coordinate. -/
def valueCLM {N P : ℕ} (c : Degree P → ℝ) (x : Vector N) :
    EuclideanDisorder N P →L[ℝ] ℝ := flatJetCLM c 0 x (fun i => Fin.elim0 i)

theorem value_intrinsic_adjoint_zero {N P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (x : Vector N) :
    (valueCLM c x).comp (intrinsicGamma c x).adjoint = 0 := by
  apply ContinuousLinearMap.ext
  intro w
  have h := congrArg (fun L : tangentPlane x →L[ℝ] EuclideanSpace ℝ (Fin 2) => L w 0)
    (score_intrinsic_adjoint_zero c hc x)
  simpa only [ContinuousLinearMap.comp_apply, scoreCLM_apply_zero,
    ContinuousLinearMap.zero_apply, PiLp.zero_apply, valueCLM, flatJetCLM_apply] using h

def jointValueTarget (n : ℕ) (b : ℝ) : EuclideanSpace ℝ (Sum (Fin 1) (Fin n)) :=
  WithLp.toLp 2 (Sum.elim (fun _ => b) (fun _ => 0))

theorem valueTangentCLM_ker_intrinsic_value {n P : ℕ} (c : Degree P → ℝ)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ)) :
    (valueTangentCLM c x (tangentFrame x hx)).ker =
      (intrinsicGamma c x).ker ⊓ (valueCLM c x).ker := by
  ext g
  change valueTangentCLM c x (tangentFrame x hx) g = 0 ↔
    intrinsicGamma c x g = 0 ∧ valueCLM c x g = 0
  rw [← tangentFrame_gradient_zero_iff c x hx g]
  constructor
  · intro h
    constructor
    · apply PiLp.ext
      intro i
      have hi := congrArg (fun v => v (Sum.inr i)) h
      simpa only [valueTangentCLM_apply_gradient, gradientCLM_apply, PiLp.zero_apply] using hi
    · have hi := congrArg (fun v => v (Sum.inl 0)) h
      simpa only [valueTangentCLM_apply_value, valueCLM, flatJetCLM_apply, PiLp.zero_apply] using hi
  · rintro ⟨hg, hv⟩
    apply PiLp.ext
    intro i
    cases i with
    | inl i => exact hv
    | inr i => exact congrArg (fun v => v i) hg

theorem center_value_surjective {n : ℕ} (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ)) :
    Surjective (valueCLM (centerCoefficients (mixtureCoefficients μ) Q) x) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hC := center_valueTangent_surjective (by omega) μ hQ x hx
    (tangentFrame x hx) (tangentFrame_orthonormal x hx) (tangentFrame_tangent x hx)
  intro b
  obtain ⟨g, hg⟩ := hC (jointValueTarget n b)
  refine ⟨g, ?_⟩
  exact congrArg (fun v => v (Sum.inl 0)) hg

theorem valueTangentCLM_value_lift {n P : ℕ} (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ))
    (hvalue : Surjective (valueCLM c x)) (b : ℝ) :
    valueTangentCLM c x (tangentFrame x hx) (lift (valueCLM c x) b) = jointValueTarget n b := by
  apply PiLp.ext
  intro i
  cases i with
  | inl i => exact observation_lift_apply _ hvalue b
  | inr i =>
    change gradientCLM c x (tangentFrame x hx) (lift (valueCLM c x) b) i = 0
    rw [tangentFrame_gradient_eq, orthogonal_observation_lift_zero _ _
      (orthogonal_observation_symm _ _ (value_intrinsic_adjoint_zero c hc x)), map_zero]
    rfl

/-- Scalar-value version of the exact full-field zero-gradient disintegration.
It applies to every mixture and in particular to the proper pure-model target. -/
theorem intrinsic_zero_value_disintegration {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ))
    (phi : Disorder (n+1) μ.maxDegree → ℝ≥0∞) (hphi : Measurable phi) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, phi J ∂coefficientKernel (intrinsicGamma c x) 0) =
      ∫⁻ b, ∫⁻ J, phi J ∂coefficientKernel (valueTangentCLM c x (tangentFrame x hx))
        (jointValueTarget n b) ∂observationLaw (valueCLM c x) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hc := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hvalue := center_value_surjective μ hQ x hx
  have h := coefficientKernel_orthogonal_zero_disintegration
    (intrinsicGamma c x) (valueCLM c x) (valueTangentCLM c x (tangentFrame x hx))
    (center_intrinsicGamma_surjective (by omega) μ hQ x hx) hvalue
    (center_valueTangent_surjective (by omega) μ hQ x hx _
      (tangentFrame_orthonormal x hx) (tangentFrame_tangent x hx))
    (orthogonal_observation_symm _ _ (value_intrinsic_adjoint_zero c hc x))
    (valueTangentCLM_ker_intrinsic_value c x hx) phi hphi
  simpa only [valueTangentCLM_value_lift c hc x hx hvalue] using h

lemma jointScoreTarget_continuous (n : ℕ) : Continuous (jointScoreTarget n) := by
  change Continuous ((PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Sum (Fin 2) (Fin n) => ℝ)).symm ∘
      (fun b : EuclideanSpace ℝ (Fin 2) => Sum.elim (fun i => b i) (fun _ => 0)))
  apply Continuous.comp (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Sum (Fin 2) (Fin n) => ℝ)).symm.continuous
  apply continuous_pi
  intro i
  cases i <;> dsimp only [Sum.elim] <;> fun_prop

lemma jointValueTarget_continuous (n : ℕ) : Continuous (jointValueTarget n) := by
  change Continuous ((PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Sum (Fin 1) (Fin n) => ℝ)).symm ∘
      (fun b : ℝ => Sum.elim (fun _ => b) (fun _ => 0)))
  apply Continuous.comp (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Sum (Fin 1) (Fin n) => ℝ)).symm.continuous
  apply continuous_pi
  intro i
  cases i <;> dsimp only [Sum.elim] <;> fun_prop

/-- Canonical explicit density of the actual normalized `(H/N,K/N)` score. -/
def normalizedScorePdf {N P : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (b : EuclideanSpace ℝ (Fin 2)) : ℝ≥0∞ :=
  observationPdf ((N : ℝ)⁻¹ • scoreCLM c x) b

/-- Canonical explicit density of the actual normalized scalar value `H/N`. -/
def normalizedValuePdf {N P : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (b : ℝ) : ℝ≥0∞ := observationPdf ((N : ℝ)⁻¹ • valueCLM c x) b

/-- The actual normalized score has this density under the original tensor
law, so the mixing density is not a substituted Gaussian model. -/
theorem normalizedScore_has_density {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ)) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    HasLaw (actualObservation (((n+1 : ℕ) : ℝ)⁻¹ • scoreCLM c x))
      (volume.withDensity (normalizedScorePdf c x)) (disorderLaw (n+1) μ.maxDegree) := by
  apply actualObservation_has_explicit_density
  exact scaled_observation_surjective _ (center_score_surjective (by omega) μ hQ hnp x hx)
    (n+1 : ℕ) (by positivity)

/-- Source conditioned-law disintegration with normalized marks: the
canonical full-field target is exactly `(N h,N k,0)`, at every `(h,k)`. -/
theorem intrinsic_zero_normalized_score_disintegration {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ))
    (phi : Disorder (n+1) μ.maxDegree → ℝ≥0∞) (hphi : Measurable phi) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, phi J ∂coefficientKernel (intrinsicGamma c x) 0) =
      ∫⁻ b, normalizedScorePdf c x b *
        ∫⁻ J, phi J ∂coefficientKernel (jointCLM c x (tangentFrame x hx))
          (jointScoreTarget n (((n+1 : ℕ) : ℝ) • b)) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hm : Measurable (fun b => ∫⁻ J, phi J
      ∂coefficientKernel (jointCLM c x (tangentFrame x hx)) (jointScoreTarget n b)) :=
    hphi.lintegral_kernel.comp (jointScoreTarget_continuous n).measurable
  dsimp only
  rw [intrinsic_zero_score_disintegration μ hQ hnp x hx phi hphi,
    lintegral_observationLaw_rescale _ (n+1 : ℕ) (by positivity) _ hm,
    observationLaw_eq_explicit_density _ (scaled_observation_surjective _
      (center_score_surjective (by omega) μ hQ hnp x hx) (n+1 : ℕ) (by positivity))]
  exact lintegral_withDensity_eq_lintegral_mul volume (observationPdf_measurable _)
    (hm.comp (by fun_prop))

/-- Scalar counterpart of the source identity, with the proper canonical
`(N h,0)` target and actual normalized-value Gaussian density. -/
theorem intrinsic_zero_normalized_value_disintegration {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ))
    (phi : Disorder (n+1) μ.maxDegree → ℝ≥0∞) (hphi : Measurable phi) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, phi J ∂coefficientKernel (intrinsicGamma c x) 0) =
      ∫⁻ b, normalizedValuePdf c x b *
        ∫⁻ J, phi J ∂coefficientKernel (valueTangentCLM c x (tangentFrame x hx))
          (jointValueTarget n ((n+1 : ℕ) * b)) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hm : Measurable (fun b => ∫⁻ J, phi J
      ∂coefficientKernel (valueTangentCLM c x (tangentFrame x hx)) (jointValueTarget n b)) :=
    hphi.lintegral_kernel.comp (jointValueTarget_continuous n).measurable
  dsimp only
  rw [intrinsic_zero_value_disintegration μ hQ x hx phi hphi,
    lintegral_observationLaw_rescale _ (n+1 : ℕ) (by positivity) _ hm,
    observationLaw_eq_explicit_density _ (scaled_observation_surjective _
      (center_value_surjective μ hQ x hx) (n+1 : ℕ) (by positivity))]
  exact lintegral_withDensity_eq_lintegral_mul volume (observationPdf_measurable _)
    (hm.comp (by fun_prop))

end
end SlowEquilibration.SphericalSequentialRegression
