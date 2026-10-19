-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalOriginalCenterObservation
public import SlowEquilibration.SphericalValueCriticalLatitudeCovariance

/-! Actual original-field score, proper-value and tangent-gradient lifts
have the literal manuscript regression multipliers, derived from true
observations and true Gram precision. -/

@[expose] public section
namespace SlowEquilibration.SphericalCriticalLatitude
noncomputable section
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet WholeFieldRegression SphericalTaylorRemainder
open SphericalParisiConditionedLatitudeCovariance IntrinsicGradientRegression SphericalForm
open SphericalMarkedWindows GaussianRegression SphericalPosteriorMaps ConditionedEntrance SphericalTwoPointCovariance
open scoped RealInnerProductSpace BigOperators Matrix
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem scalar_observation_adjoint {N P : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (f : EuclideanDisorder N P→L[ℝ] ℝ) (A : EuclideanDisorder N P→L[ℝ] F) (v : F) :
    f (A.adjoint v)=inner ℝ (A (f.adjoint 1)) v := by
  have h : f (A.adjoint v)=inner ℝ (f.adjoint 1) (A.adjoint v) := by
    rw [f.adjoint_inner_left]
    simp only [RCLike.inner_apply,RCLike.conj_to_real,mul_one]
  rw [h,A.adjoint_inner_right]

/-- The actual rescaled source conditional score mean is precisely the
literal original-field pair of regression multipliers. -/
theorem original_sourceConditionalMean_eq_theta {N : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0<Q) (hnp : μ.minDegree<μ.maxDegree) (u x : Vector N) (e k : ℝ) :
    sourceConditionalMean μ Q e k (overlap u (originalRescaledPoint Q x))=
      valueTheta μ Q (overlap x u)*e+radialTheta μ Q (overlap x u)*k := by
  unfold sourceConditionalMean
  rw [sourceCross_original_rescaling μ hQ]
  change ![μ.xi (Real.sqrt Q*overlap u x),Real.sqrt Q*overlap u x*μ.xi1 (Real.sqrt Q*overlap u x)] ⬝ᵥ
    ((μ.scoreCovariance Q)⁻¹ *ᵥ ![e,k])=_
  rw [Matrix.dotProduct_mulVec,←regression_score_row_inverse μ hQ hnp]
  simp only [dotProduct,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    overlap_comm u x]

/-- Exact physical original-field score lift at target (Ne,Nk). -/
theorem original_value_physical_score_lift {N : ℕ} (hN : 0<N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0<Q) (hnp : μ.minDegree<μ.maxDegree)
    (u : Vector N) (hu : ‖u‖^2=(N : ℝ)) (x : Vector N) (e k : ℝ) :
    valueObservation (mixtureCoefficients μ) x
      (lift (scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) u)
        ((N : ℝ) • scorePairEquiv (e,k)))=
      (N : ℝ)*(valueTheta μ Q (overlap x u)*e+radialTheta μ Q (overlap x u)*k) := by
  rw [original_valueObservation_eq_center_rescaled μ hQ x,
    center_value_score_lift hN μ hQ hnp u hu,
    original_sourceConditionalMean_eq_theta μ hQ hnp]

/-- Arbitrary actual score observations use the same true original-field lift. -/
theorem original_scoreLift_apply (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0<Q) (hnp : μ.minDegree<μ.maxDegree)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (x : Vector (n+1))
    (b : EuclideanSpace ℝ (Fin 2)) :
    valueObservation (mixtureCoefficients μ) x (scoreLift n μ Q u b)=
      valueTheta μ Q (overlap x u)*b 0+radialTheta μ Q (overlap x u)*b 1 := by
  have hN : ((n+1 : ℕ) : ℝ)≠0 := by positivity
  have hb : ((n+1 : ℕ) : ℝ) • scorePairEquiv (b 0/((n+1 : ℕ) : ℝ),b 1/((n+1 : ℕ) : ℝ))=b := by
    apply PiLp.ext
    intro i
    fin_cases i
    · change ((n+1 : ℕ) : ℝ)*(b 0/((n+1 : ℕ) : ℝ))=b 0
      field_simp
    · change ((n+1 : ℕ) : ℝ)*(b 1/((n+1 : ℕ) : ℝ))=b 1
      field_simp
  rw [scoreLift_eq n μ hQ.le u hu]
  have h := original_value_physical_score_lift (by omega) μ hQ hnp u hu x
    (b 0/((n+1 : ℕ) : ℝ)) (b 1/((n+1 : ℕ) : ℝ))
  rw [hb] at h
  rw [h]
  field_simp

/-- The proper value lift, valid also for pure mixtures, requires only
its true nonredundant one-dimensional value precision. -/
theorem original_valueLift_apply (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0<Q) (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (x : Vector (n+1)) (b : ℝ) :
    valueObservation (mixtureCoefficients μ) x (valueLift n μ Q u b)=
      μ.xi (Real.sqrt Q*overlap x u)/μ.xi Q*b := by
  have hN : ((n+1 : ℕ) : ℝ)≠0 := by positivity
  have he : Q*overlap u (originalRescaledPoint Q x)=Real.sqrt Q*overlap x u := by
    have hs : Real.sqrt Q≠0 := (Real.sqrt_pos.mpr hQ).ne'
    unfold overlap originalRescaledPoint
    rw [real_inner_smul_right,real_inner_comm x u]
    field_simp [hs,hN]
    rw [Real.sq_sqrt hQ.le]
  rw [original_valueObservation_eq_center_rescaled μ hQ x,valueLift_eq n μ hQ.le u hu]
  have h := center_value_only_lift n μ hQ u hu (originalRescaledPoint Q x) (b/((n+1 : ℕ) : ℝ))
  rw [mul_div_cancel₀ b hN,he] at h
  rw [h]
  field_simp

/-- Literal source tangent multiplier of the true original-field gradient lift. -/
theorem original_gradient_lift_apply {N : ℕ} (hN : 0<N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0<Q) (u : Vector N) (hu : ‖u‖^2=(N : ℝ))
    (x : Vector N) (v : tangentPlane u) :
    valueObservation (mixtureCoefficients μ) x
      (lift (intrinsicGamma (centerCoefficients (mixtureCoefficients μ) Q) u) v)=
      tangentTheta μ Q (overlap x u)*inner ℝ (v : Vector N) x := by
  unfold lift
  rw [ContinuousLinearMap.comp_apply,scalar_observation_adjoint,
    center_gradient_inverse_apply hN μ hQ u hu,original_gradient_value_cross hN μ hQ,
    real_inner_smul_left,real_inner_smul_right]
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  rw [real_inner_comm x (v : Vector N)]
  rw [tangentTheta_eq,overlap_comm u x]
  unfold aScore
  ring

end
end SlowEquilibration.SphericalCriticalLatitude
