-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.NormalizedPairObservations
public import SlowEquilibration.GaussianObservationLowerBound
public import SlowEquilibration.SphericalScoreDensity

/-! Genuine dimension-independent one-point observation coercivity. The
score constant is chosen from a fixed one-dimensional actual field; the
normalized Gram is literally identical in every spatial dimension. -/
@[expose] public section
namespace SlowEquilibration.NormalizedObservationCoercivity
noncomputable section
open Function MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open GaussianRegression GaussianObservationCoercivity SphericalPairRegression
open SphericalSequentialRegression
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

def referencePoint : Vector 1 := EuclideanSpace.basisFun (Fin 1) ℝ 0
lemma referencePoint_norm_sq : ‖referencePoint‖^2=(1:ℝ) := by
  rw [referencePoint,(EuclideanSpace.basisFun (Fin 1) ℝ).orthonormal.norm_eq_one]
  norm_num

lemma sqrtNormalized_score_gram_matrix {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (x : Vector N) (hx : ‖x‖^2=(N:ℝ)) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (gram ((Real.sqrt (N:ℝ))⁻¹ • scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) x)).toLinearMap=
      μ.scoreCovariance Q := by
  rw [gram_smul_real,ContinuousLinearMap.toLinearMap_smul,map_smul,
    center_score_gram_matrix hN μ hQ x hx,smul_smul]
  have hn : (Real.sqrt (N:ℝ))⁻¹^2*(N:ℝ)=1 := by
    rw [inv_pow,Real.sq_sqrt (Nat.cast_nonneg N)]
    exact inv_mul_cancel₀ (by positivity)
  rw [hn,one_smul]

lemma sqrtNormalized_score_gram_eq_reference {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (x : Vector N) (hx : ‖x‖^2=(N:ℝ)) :
    gram ((Real.sqrt (N:ℝ))⁻¹ • scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) x)=
      gram (scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) referencePoint) := by
  apply ContinuousLinearMap.coe_injective
  apply (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis).injective
  rw [sqrtNormalized_score_gram_matrix hN μ hQ x hx,
    center_score_gram_matrix (by norm_num) μ hQ referencePoint (by simpa using referencePoint_norm_sq)]
  simp

/-- The score lower bound is selected before N and the sphere point. -/
theorem uniform_score_coercivity (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) :
    ∃ α : ℝ,0 < α ∧ ∀ (N : ℕ) (_hN : 0 < N) (x : Vector N),
      ‖x‖^2=(N:ℝ) → CoerciveObservation
        ((Real.sqrt (N:ℝ))⁻¹ • scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) x) α := by
  obtain ⟨α,hα,hA⟩:=exists_coercivity_of_surjective
    (scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) referencePoint)
    (center_score_surjective (by norm_num) μ hQ hnp referencePoint (by simpa using referencePoint_norm_sq))
  refine ⟨α,hα,?_⟩
  intro N hN x hx u
  rw [← gram_inner,sqrtNormalized_score_gram_eq_reference hN μ hQ.le x hx,gram_inner]
  exact hA u

lemma gradient_coercivity {N m : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (x : Vector N) (hx : ‖x‖^2=(N:ℝ))
    (e : Fin m → Vector N) (he : Orthonormal ℝ e) (htan : ∀ i,inner ℝ (e i) x=0) :
    CoerciveObservation (gradientCLM (centerCoefficients (mixtureCoefficients μ) Q) x e) (Q*μ.xi1 Q) := by
  intro v
  rw [← gram_inner,gradient_gram hN _
    (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le) x hx e he htan,
    firstCovariance_center,firstCovariance_mixture]
  simp only [smul_apply,ContinuousLinearMap.id_apply,inner_smul_right,real_inner_self_eq_norm_sq,le_refl]

lemma score_gradient_cross_zero {N P m : ℕ} (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p)
    (x : Vector N) (e : Fin m → Vector N) (htan : ∀ i,inner ℝ (e i) x=0) :
    (scoreCLM c x).comp (gradientCLM c x e).adjoint=0 := by
  apply cross_zero_of_coordinate_covariances
  intro i j
  fin_cases i
  · simpa [actualObservation,scoreCLM]
      using value_tangent_gradient_covariance_zero c hc x (e j) (htan j)
  · simpa [actualObservation,scoreCLM]
      using radial_tangent_gradient_covariance_zero c hc x (e j) (htan j)

/-- Genuine single-point mixed coercivity, chosen before every dimension,
point and orthonormal tangent frame. -/
theorem uniform_mixed_coercivity (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) :
    ∃ δ : ℝ,0 < δ ∧ ∀ (N m : ℕ) (_hN : 0 < N) (x : Vector N),
      ‖x‖^2=(N:ℝ) → ∀ (e : Fin m → Vector N),Orthonormal ℝ e →
        (∀ i,inner ℝ (e i) x=0) →
      CoerciveObservation (singleMixedObservation (centerCoefficients (mixtureCoefficients μ) Q) x e) δ := by
  obtain ⟨α,hα,hscore⟩:=uniform_score_coercivity μ hQ hnp
  let a:=Q*μ.xi1 Q
  have ha : 0 < a := mul_pos hQ (mixture_xi1_pos μ hQ)
  have hmin : 0 < min α a := lt_min hα ha
  refine ⟨min α a/2,by positivity,?_⟩
  intro N m hN x hx e he htan
  apply pair_coercive _ _ hmin
  · intro u
    exact (mul_le_mul_of_nonneg_right (min_le_left α a) (sq_nonneg _)).trans (hscore N hN x hx u)
  · intro v
    exact (mul_le_mul_of_nonneg_right (min_le_right α a) (sq_nonneg _)).trans
      (gradient_coercivity hN μ hQ x hx e he htan v)
  · have hz:=score_gradient_cross_zero (centerCoefficients (mixtureCoefficients μ) Q)
      (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le) x e htan
    simp only [ContinuousLinearMap.smul_comp,hz,smul_zero,norm_zero]
    positivity

lemma sqrtNormalized_value_gram {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (x : Vector N) (hx : ‖x‖^2=(N:ℝ)) :
    gram ((Real.sqrt (N:ℝ))⁻¹ • valueCLM (centerCoefficients (mixtureCoefficients μ) Q) x)=
      μ.xi Q • ContinuousLinearMap.id ℝ ℝ := by
  rw [gram_smul_real,center_value_gram hN μ hQ x hx,smul_smul]
  have hn : (Real.sqrt (N:ℝ))⁻¹^2*(N:ℝ)=1 := by
    rw [inv_pow,Real.sq_sqrt (Nat.cast_nonneg N)]
    exact inv_mul_cancel₀ (by positivity)
  rw [← mul_assoc,hn,one_mul]

lemma value_gradient_cross_zero {N P m : ℕ} (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p)
    (x : Vector N) (e : Fin m → Vector N) (htan : ∀ i,inner ℝ (e i) x=0) :
    (valueCLM c x).comp (gradientCLM c x e).adjoint=0 := by
  have he : valueCLM c x=(EuclideanSpace.proj (0 : Fin 2)).comp (scoreCLM c x) := by
    ext g
    simp only [valueCLM,flatJetCLM_apply,ContinuousLinearMap.comp_apply,
      EuclideanSpace.proj,PiLp.proj_apply,scoreCLM_apply_zero]
  rw [he,ContinuousLinearMap.comp_assoc,score_gradient_cross_zero c hc x e htan,
    ContinuousLinearMap.comp_zero]

/-- The proper value/tangent observation is uniformly coercive in every
finite mixture, including pure models. No nonpurity hypothesis is needed. -/
theorem uniform_value_coercivity (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) :
    ∃ δ : ℝ,0 < δ ∧ ∀ (N m : ℕ) (_hN : 0 < N) (x : Vector N),
      ‖x‖^2=(N:ℝ) → ∀ (e : Fin m → Vector N),Orthonormal ℝ e →
        (∀ i,inner ℝ (e i) x=0) →
      CoerciveObservation (singleValueObservation (centerCoefficients (mixtureCoefficients μ) Q) x e) δ := by
  let a:=Q*μ.xi1 Q
  have ha : 0 < a := mul_pos hQ (mixture_xi1_pos μ hQ)
  have hxi:=μ.xi_pos hQ
  have hmin : 0 < min (μ.xi Q) a := lt_min hxi ha
  refine ⟨min (μ.xi Q) a/2,by positivity,?_⟩
  intro N m hN x hx e he htan
  apply pair_coercive _ _ hmin
  · intro u
    change min (μ.xi Q) a*‖u‖^2 ≤
      ‖((Real.sqrt (N:ℝ))⁻¹ • valueCLM (centerCoefficients (mixtureCoefficients μ) Q) x).adjoint u‖^2
    rw [← gram_inner,sqrtNormalized_value_gram hN μ hQ.le x hx]
    simp only [smul_apply,ContinuousLinearMap.id_apply,inner_smul_right,real_inner_self_eq_norm_sq]
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
  · intro v
    exact (mul_le_mul_of_nonneg_right (min_le_right (μ.xi Q) a) (sq_nonneg _)).trans
      (gradient_coercivity hN μ hQ x hx e he htan v)
  · have hz:=value_gradient_cross_zero (centerCoefficients (mixtureCoefficients μ) Q)
      (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le) x e htan
    change ‖((Real.sqrt (N:ℝ))⁻¹ • valueCLM _ x).comp (gradientCLM _ x e).adjoint‖ ≤ _
    simp only [ContinuousLinearMap.smul_comp,hz,smul_zero,norm_zero]
    positivity

end
end SlowEquilibration.NormalizedObservationCoercivity
