-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalCriticalLatitudeContinuousLaw
public import SlowEquilibration.SphericalParisiConditionedLatitudeCovariance
public import SlowEquilibration.CenterCovarianceDerivativeScaling
public import SlowEquilibration.SphericalCountRectangles

/-! Exact physical score contractions in the actual critical-conditioned
latitude field. The source mean follows from the true covariance inverse
and the literal coefficient observation, with every N factor retained. -/

@[expose] public section
namespace SlowEquilibration.SphericalCriticalLatitude
noncomputable section
open MeasureTheory ProbabilityTheory Function
open SphericalModel SphericalGaussianJet WholeFieldRegression SphericalPosteriorMaps
open SphericalTaylorRemainder SphericalSequentialRegression SphericalMarkedWindows
open SphericalTwoPointCovariance GaussianRegression
open SphericalParisiConditionedLatitudeCovariance
open scoped RealInnerProductSpace Matrix
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal physical score inverse acts by N⁻¹Σ_Q⁻¹. -/
theorem center_physical_score_inverse_apply {N : ℕ} (hN : 0 < N)
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (u : Vector N) (hu : ‖u‖^2=(N : ℝ)) (b : EuclideanSpace ℝ (Fin 2)) :
    (fun i => (gram (scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) u)).inverse b i)=
      (N : ℝ)⁻¹ • ((μ.scoreCovariance Q)⁻¹ *ᵥ (fun i => b i)) := by
  let A := scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) u
  have hA := center_score_surjective hN μ hQ hnp u hu
  have hi := LinearMap.toMatrix_mulVec_repr
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis (gram A).toLinearMap ((gram A).inverse b)
  rw [center_score_gram_matrix hN μ hQ.le u hu] at hi
  have hs := (gram_isInvertible A hA).self_apply_inverse b
  change ((N : ℝ) • μ.scoreCovariance Q) *ᵥ
    (fun i => (gram A).inverse b i)=(fun i => gram A ((gram A).inverse b) i) at hi
  rw [hs] at hi
  have hn : (N : ℝ)≠0 := by positivity
  have hd : IsUnit (μ.scoreCovariance Q).det :=
    isUnit_iff_ne_zero.mpr (μ.scoreCovariance_det_pos hQ hnp).ne'
  have hh := congrArg (fun v => (μ.scoreCovariance Q)⁻¹ *ᵥ ((N : ℝ)⁻¹ • v)) hi
  simpa only [Matrix.smul_mulVec,smul_smul,inv_mul_cancel₀ hn,one_smul,
    Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ hd,Matrix.one_mulVec,Matrix.mulVec_smul] using hh

/-- Actual physical value/score cross covariance at every overlap. -/
theorem center_score_value_cross {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (u w : Vector N) :
    scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) u
      ((valueObservation (centerCoefficients (mixtureCoefficients μ) Q) w).adjoint 1)=
        (N : ℝ) • sourceCross μ Q (overlap u w) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hc := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ
  apply PiLp.ext
  intro i
  fin_cases i
  · change valueObservation c u ((valueObservation c w).adjoint 1)=
      (N : ℝ)*μ.xi (Q*overlap u w)
    rw [value_value_coupling hN c hc,covariancePolynomial_center,covariancePolynomial_mixture]
  · change directionObservation c u u ((valueObservation c w).adjoint 1)=
      (N : ℝ)*(overlap u w*(Q*μ.xi1 (Q*overlap u w)))
    rw [direction_value_coupling hN c hc,firstCovariance_center_at,
      firstCovariance_mixture,inner_eq_dimension_overlap hN u w]
    ring

private theorem scalar_adjoint_value {N P : ℕ}
    (f : EuclideanDisorder N P →L[ℝ] ℝ)
    (A : EuclideanDisorder N P →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (v : EuclideanSpace ℝ (Fin 2)) :
    f (A.adjoint v)=inner ℝ (A (f.adjoint 1)) v := by
  have h : f (A.adjoint v)=inner ℝ (f.adjoint 1) (A.adjoint v) := by
    rw [f.adjoint_inner_left]
    simp only [RCLike.inner_apply,RCLike.conj_to_real,mul_one]
  rw [h,A.adjoint_inner_right]

/-- The source conditional mean is the actual finite-coefficient score
lift evaluated at the target (Ne,Nk,0). -/
theorem center_value_score_lift {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (u : Vector N) (hu : ‖u‖^2=(N : ℝ)) (w : Vector N) (e k : ℝ) :
    valueObservation (centerCoefficients (mixtureCoefficients μ) Q) w
      (lift (scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) u)
        ((N : ℝ) • scorePairEquiv (e,k)))=
      (N : ℝ)*sourceConditionalMean μ Q e k (overlap u w) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let A := scoreCLM c u
  let b := scorePairEquiv (e,k)
  have hn : (N : ℝ)≠0 := by positivity
  have hi : (fun i => (gram A).inverse ((N : ℝ) • b) i)=
      (μ.scoreCovariance Q)⁻¹ *ᵥ (fun i => b i) := by
    rw [center_physical_score_inverse_apply hN μ hQ hnp u hu]
    change (N : ℝ)⁻¹ • ((μ.scoreCovariance Q)⁻¹ *ᵥ ((N : ℝ) • (fun i => b i)))=_
    rw [Matrix.mulVec_smul,smul_smul,inv_mul_cancel₀ hn,one_smul]
  change valueObservation c w (A.adjoint ((gram A).inverse ((N : ℝ) • b)))=_
  rw [scalar_adjoint_value,center_score_value_cross hN μ hQ.le u w]
  simp only [sourceConditionalMean,dotProduct,PiLp.inner_apply,RCLike.inner_apply,
    RCLike.conj_to_real,PiLp.smul_apply,smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [congrFun hi i]
  ring

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

omit [CompactSpace K] in
/-- The deterministic mean function of the actual conditioned continuous
field is exactly the manuscript mean at the literal overlap. -/
theorem criticalContinuousMean_eq_source (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (z : K → Vector (n+1)) (hz : Continuous z) (e k : ℝ) (v : K) :
    criticalContinuousMean n μ Q u z hz (scorePairEquiv (e,k)) v=
      (n+1 : ℕ)*sourceConditionalMean μ Q e k (overlap u (z v)) := by
  unfold criticalContinuousMean criticalContinuousField
  rw [modelContinuousField_apply,scoreLift_eq n μ hQ.le u hu]
  exact center_value_score_lift (by omega) μ hQ hnp u hu (z v) e k

end
end SlowEquilibration.SphericalCriticalLatitude
