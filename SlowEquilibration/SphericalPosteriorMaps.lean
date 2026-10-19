-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureMarkedWindows

/-! Continuous, frame-independent affine maps for the actual full-disorder posteriors. -/

@[expose] public section
namespace SlowEquilibration.SphericalPosteriorMaps

open MeasureTheory ProbabilityTheory Set Function
open SphericalModel SphericalGaussianJet WholeFieldRegression IntrinsicGradientRegression
open IntrinsicHessianLaw GaussianRegression SphericalSequentialRegression SphericalForm
open SphereHessian SphereChartVolume SphericalKacRiceGluing SphericalMarkedWindows
open ValueTangentConditioning
open scoped ENNReal Topology RealInnerProductSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

abbrev SpherePoint (n : ℕ) := {x : Vector (n+1) | ‖x‖ ^ 2 = (n+1 : ℕ)}

def surfaceGamma {N P : ℕ} (c : Degree P → ℝ) (x : Vector N) :
    EuclideanDisorder N P →L[ℝ] Vector N :=
  (tangentProjection x).comp (ambientGradientCLM c x)

lemma ambientGradientCLM_continuous {N P : ℕ} (c : Degree P → ℝ) :
    Continuous (ambientGradientCLM (N := N) c) := by
  apply continuous_clm_apply.mpr
  intro g
  simpa only [ambientGradientCLM_apply] using
    (field_gradient_contDiff c (unpackDisorder g)).continuous

lemma surfaceGamma_continuous {N P : ℕ} (c : Degree P → ℝ) :
    Continuous (surfaceGamma (N := N) c) :=
  (tangentProjection_continuous N).clm_comp (ambientGradientCLM_continuous c)

lemma surfaceGamma_eq_intrinsic {N P : ℕ} (hN : N ≠ 0) (c : Degree P → ℝ)
    (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ)) (g : EuclideanDisorder N P) :
    surfaceGamma c x g = (intrinsicGamma c x g : Vector N) := by
  rw [intrinsicGamma_coe hN c x hx, surfaceGamma, ContinuousLinearMap.comp_apply,
    ambientGradientCLM_apply]
  rfl

lemma surfaceGamma_adjoint_self {N P : ℕ} (hN : N ≠ 0) (c : Degree P → ℝ)
    (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ)) :
    (surfaceGamma c x).adjoint.comp (surfaceGamma c x) =
      (intrinsicGamma c x).adjoint.comp (intrinsicGamma c x) := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℝ
  intro v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    surfaceGamma_eq_intrinsic hN c x hx]
  rfl

lemma scoreCLM_continuous {N P : ℕ} (c : Degree P → ℝ) :
    Continuous (scoreCLM (N := N) c) := by
  apply continuous_clm_apply.mpr
  intro g
  change Continuous ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm ∘
    (fun x : Vector N => fun i => scoreCLM c x g i))
  apply Continuous.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.continuous
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun x : Vector N => scoreCLM c x g 0)
    simp only [scoreCLM_apply_zero, jet, iteratedFDeriv_zero_apply]
    exact (field_contDiff c (unpackDisorder g)).continuous
  · change Continuous (fun x : Vector N => scoreCLM c x g 1)
    simp only [scoreCLM_apply_one, jet, iteratedFDeriv_one_apply, ← inner_gradient_left]
    exact (field_gradient_contDiff c (unpackDisorder g)).continuous.inner continuous_id

lemma valueCLM_continuous {N P : ℕ} (c : Degree P → ℝ) :
    Continuous (valueCLM (N := N) c) := by
  apply continuous_clm_apply.mpr
  intro g
  simpa only [valueCLM, flatJetCLM_apply, jet, iteratedFDeriv_zero_apply] using
    (field_contDiff c (unpackDisorder g)).continuous

/-- The genuine zero-gradient coefficient projection, extended continuously
away from the sphere by the ambient polynomial formula. -/
def gradientResidual (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (x : Vector (n+1)) :
    EuclideanDisorder (n+1) μ.maxDegree →L[ℝ] EuclideanDisorder (n+1) μ.maxDegree :=
  ContinuousLinearMap.id ℝ _ - (Q * μ.xi1 Q)⁻¹ •
    (surfaceGamma (centerCoefficients (mixtureCoefficients μ) Q) x).adjoint.comp
      (surfaceGamma (centerCoefficients (mixtureCoefficients μ) Q) x)

lemma gradientResidual_continuous (n : ℕ) (μ : FiniteMixture) (Q : ℝ) :
    Continuous (gradientResidual n μ Q) := by
  have hc := surfaceGamma_continuous (N := n+1) (centerCoefficients (mixtureCoefficients μ) Q)
  unfold gradientResidual
  apply continuous_const.sub
  convert (((ContinuousLinearMap.adjoint.continuous.comp hc).clm_comp hc).const_smul
    ((Q * μ.xi1 Q)⁻¹)) using 1
  funext x
  rfl

lemma gradientResidual_eq (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ)) :
    gradientResidual n μ Q x = residual (intrinsicGamma (centerCoefficients (mixtureCoefficients μ) Q) x) := by
  let A := intrinsicGamma (centerCoefficients (mixtureCoefficients μ) Q) x
  let a := Q * μ.xi1 Q
  have ha : a ≠ 0 := (mul_pos hQ (mixture_xi1_pos μ hQ)).ne'
  have hA := center_intrinsicGamma_surjective (by omega) μ hQ x hx
  have hi (b : tangentPlane x) : (gram A).inverse b = a⁻¹ • b := by
    have hg := center_intrinsicGamma_gram (by omega) μ hQ.le x hx
    have he := congrArg (fun T => T ((gram A).inverse b)) hg
    have h : a • (gram A).inverse b = b :=
      he.symm.trans ((gram_isInvertible A hA).self_apply_inverse b)
    calc
      _ = a⁻¹ • (a • (gram A).inverse b) := (inv_smul_smul₀ ha _).symm
      _ = _ := congrArg (fun z => a⁻¹ • z) h
  rw [gradientResidual, surfaceGamma_adjoint_self (by omega) _ x hx]
  apply ContinuousLinearMap.ext
  intro g
  change g - a⁻¹ • A.adjoint (A g) = g - A.adjoint ((gram A).inverse (A g))
  rw [hi, map_smul]

lemma score_gram_eq_pole (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 ≤ Q)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ)) :
    gram (scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) x) =
      gram (scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) (southPole n)) := by
  have he := (center_score_gram_matrix (by omega) μ hQ x hx).trans
    (center_score_gram_matrix (by omega) μ hQ _ (southPole_norm_sq n)).symm
  have hlin := (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis).injective he
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun L : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) => L v) hlin

/-- The same true score lift at every sphere point, with its fixed score
covariance displayed to make its continuous dependence explicit. -/
def scoreLift (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (x : Vector (n+1)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanDisorder (n+1) μ.maxDegree :=
  (scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) x).adjoint.comp
    (gram (scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) (southPole n))).inverse

lemma scoreLift_continuous (n : ℕ) (μ : FiniteMixture) (Q : ℝ) :
    Continuous (scoreLift n μ Q) :=
  (ContinuousLinearMap.adjoint.continuous.comp (scoreCLM_continuous _)).clm_comp continuous_const

lemma scoreLift_eq (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 ≤ Q)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ)) :
    scoreLift n μ Q x = lift (scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) x) := by
  rw [lift, score_gram_eq_pole n μ hQ x hx]
  rfl


def scoreResidual (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (x : Vector (n+1)) :
    EuclideanDisorder (n+1) μ.maxDegree →L[ℝ] EuclideanDisorder (n+1) μ.maxDegree :=
  ContinuousLinearMap.id ℝ _ - (scoreLift n μ Q x).comp
    (scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) x)

lemma scoreResidual_continuous (n : ℕ) (μ : FiniteMixture) (Q : ℝ) :
    Continuous (scoreResidual n μ Q) :=
  continuous_const.sub ((scoreLift_continuous n μ Q).clm_comp (scoreCLM_continuous _))

lemma scoreResidual_eq (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 ≤ Q)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ)) :
    scoreResidual n μ Q x = GaussianRegression.residual
      (scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) x) := by
  rw [scoreResidual, scoreLift_eq n μ hQ x hx]
  rfl

def valueLift (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (x : Vector (n+1)) :
    ℝ →L[ℝ] EuclideanDisorder (n+1) μ.maxDegree :=
  (valueCLM (centerCoefficients (mixtureCoefficients μ) Q) x).adjoint.comp
    (((n+1 : ℕ) * μ.xi Q) • ContinuousLinearMap.id ℝ ℝ).inverse

lemma valueLift_continuous (n : ℕ) (μ : FiniteMixture) (Q : ℝ) :
    Continuous (valueLift n μ Q) :=
  (ContinuousLinearMap.adjoint.continuous.comp (valueCLM_continuous _)).clm_comp continuous_const

lemma valueLift_eq (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 ≤ Q)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ)) :
    valueLift n μ Q x = lift (valueCLM (centerCoefficients (mixtureCoefficients μ) Q) x) := by
  rw [lift, center_value_gram (by omega) μ hQ x hx]
  rfl

def valueResidual (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (x : Vector (n+1)) :
    EuclideanDisorder (n+1) μ.maxDegree →L[ℝ] EuclideanDisorder (n+1) μ.maxDegree :=
  ContinuousLinearMap.id ℝ _ - (valueLift n μ Q x).comp
    (valueCLM (centerCoefficients (mixtureCoefficients μ) Q) x)

lemma valueResidual_continuous (n : ℕ) (μ : FiniteMixture) (Q : ℝ) :
    Continuous (valueResidual n μ Q) :=
  continuous_const.sub ((valueLift_continuous n μ Q).clm_comp (valueCLM_continuous _))

lemma valueResidual_eq (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 ≤ Q)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ)) :
    valueResidual n μ Q x = GaussianRegression.residual
      (valueCLM (centerCoefficients (mixtureCoefficients μ) Q) x) := by
  rw [valueResidual, valueLift_eq n μ hQ x hx]
  rfl

/-- All original Gaussian coefficients after mixed score and gradient conditioning. -/
def mixedPosterior (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (x : Vector (n+1))
    (b : EuclideanSpace ℝ (Fin 2)) (g : EuclideanDisorder (n+1) μ.maxDegree) :
    EuclideanDisorder (n+1) μ.maxDegree :=
  gradientResidual n μ Q x (scoreResidual n μ Q x g) +
    scoreLift n μ Q x (((n+1 : ℕ) : ℝ) • b)

lemma mixedPosterior_continuous (n : ℕ) (μ : FiniteMixture) (Q : ℝ) :
    Continuous (fun p : (Vector (n+1) × EuclideanSpace ℝ (Fin 2)) ×
      EuclideanDisorder (n+1) μ.maxDegree => mixedPosterior n μ Q p.1.1 p.1.2 p.2) := by
  unfold mixedPosterior
  exact ((gradientResidual_continuous n μ Q).comp continuous_fst.fst |>.clm_apply
    ((scoreResidual_continuous n μ Q).comp continuous_fst.fst |>.clm_apply continuous_snd)).add
      ((scoreLift_continuous n μ Q).comp continuous_fst.fst |>.clm_apply
        (by fun_prop))

/-- The proper scalar-value posterior, also valid for pure mixtures. -/
def valuePosterior (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (x : Vector (n+1))
    (b : ℝ) (g : EuclideanDisorder (n+1) μ.maxDegree) :
    EuclideanDisorder (n+1) μ.maxDegree :=
  gradientResidual n μ Q x (valueResidual n μ Q x g) +
    valueLift n μ Q x ((n+1 : ℕ) * b)

lemma valuePosterior_continuous (n : ℕ) (μ : FiniteMixture) (Q : ℝ) :
    Continuous (fun p : (Vector (n+1) × ℝ) × EuclideanDisorder (n+1) μ.maxDegree =>
      valuePosterior n μ Q p.1.1 p.1.2 p.2) := by
  unfold valuePosterior
  exact ((gradientResidual_continuous n μ Q).comp continuous_fst.fst |>.clm_apply
    ((valueResidual_continuous n μ Q).comp continuous_fst.fst |>.clm_apply continuous_snd)).add
      ((valueLift_continuous n μ Q).comp continuous_fst.fst |>.clm_apply
        (continuous_const.mul continuous_fst.snd))

lemma coefficientKernel_orthogonal_map {N P : ℕ} {F G H : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    (A : EuclideanDisorder N P →L[ℝ] F) (B : EuclideanDisorder N P →L[ℝ] G)
    (C : EuclideanDisorder N P →L[ℝ] H)
    (hA : Surjective A) (hB : Surjective B) (hC : Surjective C)
    (hAB : A.comp B.adjoint = 0) (hker : C.ker = A.ker ⊓ B.ker) (b : G) :
    coefficientKernel C (C (lift B b)) = (stdGaussian (EuclideanDisorder N P)).map
      (fun g => unpackCLM N P (GaussianRegression.residual A
        (GaussianRegression.residual B g) + lift B b)) := by
  rw [coefficientKernel_apply, regressionKernel_apply,
    Measure.map_map (unpackCLM N P).continuous.measurable (by fun_prop),
    orthogonal_joint_residual A B C hA hB hC hAB hker,
    orthogonal_joint_lift B C hC (by rw [hker]; exact inf_le_right)]
  rfl

lemma mixedConditionedLaw_eq_map (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ))
    (b : EuclideanSpace ℝ (Fin 2)) :
    mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) x hx b =
      (stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)).map
        (fun g => unpackCLM (n+1) μ.maxDegree (mixedPosterior n μ Q x b g)) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hc := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hs := center_score_surjective (by omega) μ hQ hnp x hx
  have h := coefficientKernel_orthogonal_map (intrinsicGamma c x) (scoreCLM c x)
    (jointCLM c x (tangentFrame x hx))
    (center_intrinsicGamma_surjective (by omega) μ hQ x hx) hs
    (center_joint_surjective (by omega) μ hQ hnp x hx _
      (tangentFrame_orthonormal x hx) (tangentFrame_tangent x hx))
    (orthogonal_observation_symm _ _ (score_intrinsic_adjoint_zero c hc x))
    (jointCLM_ker_intrinsic_score c x hx) (((n+1 : ℕ) : ℝ) • b)
  rw [jointCLM_score_lift c hc x hx hs] at h
  simpa only [mixedConditionedLaw, mixedPosterior, gradientResidual_eq n μ hQ x hx,
    scoreResidual_eq n μ hQ.le x hx, scoreLift_eq n μ hQ.le x hx] using h

lemma valueConditionedLaw_eq_map (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ)) (b : ℝ) :
    valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) x hx b =
      (stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)).map
        (fun g => unpackCLM (n+1) μ.maxDegree (valuePosterior n μ Q x b g)) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hc := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hs := center_value_surjective μ hQ x hx
  have h := coefficientKernel_orthogonal_map (intrinsicGamma c x) (valueCLM c x)
    (valueTangentCLM c x (tangentFrame x hx))
    (center_intrinsicGamma_surjective (by omega) μ hQ x hx) hs
    (center_valueTangent_surjective (by omega) μ hQ x hx _
      (tangentFrame_orthonormal x hx) (tangentFrame_tangent x hx))
    (orthogonal_observation_symm _ _ (value_intrinsic_adjoint_zero c hc x))
    (valueTangentCLM_ker_intrinsic_value c x hx) ((n+1 : ℕ) * b)
  rw [valueTangentCLM_value_lift c hc x hx hs] at h
  simpa only [valueConditionedLaw, valuePosterior, gradientResidual_eq n μ hQ x hx,
    valueResidual_eq n μ hQ.le x hx, valueLift_eq n μ hQ.le x hx] using h

lemma intrinsic_zero_kernel_eq_map (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ)) :
    coefficientKernel (intrinsicGamma (centerCoefficients (mixtureCoefficients μ) Q) x) 0 =
      (stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)).map
        (fun g => unpackCLM (n+1) μ.maxDegree (gradientResidual n μ Q x g)) := by
  rw [coefficientKernel_apply, regressionKernel_apply,
    Measure.map_map (unpackCLM _ _).continuous.measurable (by fun_prop),
    gradientResidual_eq n μ hQ x hx]
  simp only [map_zero, add_zero, Function.comp_def]

end
end SlowEquilibration.SphericalPosteriorMaps
