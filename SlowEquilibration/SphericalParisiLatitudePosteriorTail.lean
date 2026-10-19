-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiLatitudePosteriorGround
public import SlowEquilibration.SourcePhysicalPairAffineSupremumConcentration
public import SlowEquilibration.SourcePhysicalPairPosteriorJetConcentration

@[expose] public section

/-! True original conditional-latitude maximum concentration. The actual
coefficient kernel is represented by its orthogonal Gaussian residual and
canonical observation lift. Its supremum Lipschitz constant is derived
from the genuine original covariance budget N*xi(Q), uniformly in marks.
The actual HS-derived mean is then consumed to give a real exponential
fixed-latitude posterior height bound. -/

namespace SlowEquilibration.SphericalParisiLatitudePosteriorTail
noncomputable section
open MeasureTheory ProbabilityTheory Set Function Filter
open SphericalModel FiniteTensorMixtureMaximum PureTensorJetBounds
open SphericalGaussianJet WholeFieldRegression GaussianRegression SphericalPosteriorMaps
open SphericalMarkedWindows SphericalSequentialRegression ValueTangentConditioning IntrinsicHessianLaw
open SphericalTaylorRemainder SphericalCriticalLatitude SphericalParisiConditionedLatitudeCovariance
open SphericalParisiLatitudePosteriorGround SphericalParisiContinuousMaximum
open PairConditionalDeterminantMoments LatitudeGroundTrial GaussianCompactMaximum
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem mixedLatitudeMaximum_measurable {n : ℕ} (hn : 0 < n)
    (μ : FiniteMixture) (Q r : ℝ) (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) : Measurable (mixedLatitudeMaximum n μ Q r u e) := by
  let : NeZero n := ⟨hn.ne'⟩
  have H := maximum_measurable.comp ((mixedLatitudeContinuousField n μ Q r u e).continuous.measurable.comp
    (SphericalTaylorRemainder.euclideanDisorder_measurable _ _))
  convert H using 1
  funext J
  exact mixedLatitudeMaximum_eq_maximum hn μ Q r u e J

/-- Actual coefficient-kernel concentration for the original physical
latitude maximum after any genuine surjective finite observation. -/
theorem actual_coefficient_kernel_latitude_centered_tail {n : ℕ} (hn : 0 < n)
    (μ : FiniteMixture) {Q r : ℝ} (hQ : 0 < Q) (hr : r∈Ioo (0 : ℝ) 1)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x,inner ℝ (e x) u=0)
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (A : EuclideanDisorder (n+1) μ.maxDegree →L[ℝ] F) (hA : Surjective A) (w : F)
    {t : ℝ} (ht : 0 ≤ t) :
    (coefficientKernel A w).real
      {J | (∫ K,mixedLatitudeMaximum n μ Q r u e K ∂coefficientKernel A w)+
        ((n+1 : ℕ) : ℝ)*t ≤ mixedLatitudeMaximum n μ Q r u e J} ≤
      Real.exp (-((n+1 : ℕ) : ℝ)*t^2/(2*μ.xi Q)) := by
  classical
  let : NeZero n := ⟨hn.ne'⟩
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let L : UnitSphere n → EuclideanDisorder (n+1) μ.maxDegree →L[ℝ] ℝ :=
    fun x => sphereLinear c (sourceUnitLatitudeMap u e r x.val)
  let B := Real.sqrt (((n+1 : ℕ) : ℝ)*μ.xi Q)
  let G := SYK.standardGaussianMeasureOnEuclidean (SphericalModel.Coordinate (n+1) μ.maxDegree)
  let P := coefficientKernel A w
  let Y := fun g : EuclideanDisorder (n+1) μ.maxDegree =>
    unpackCLM (n+1) μ.maxDegree (residual A g+lift A w)
  have hYr : Measurable Y := (unpackCLM _ _).continuous.measurable.comp (by fun_prop)
  have hLaw : HasLaw Y P G := ⟨hYr.aemeasurable,(sourceCoefficientKernel_affine A w).symm⟩
  have hM := mixedLatitudeMaximum_measurable hn μ Q r u e
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hN : (0 : ℝ) < (n+1 : ℕ) := by positivity
  have hvar : 0 < μ.xi Q := μ.xi_pos hQ
  have hcoeff := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hBound (x : UnitSphere n) : ‖L x‖ ≤ B := by
    have hz : ‖sourceUnitLatitudeMap u e r x.val‖^2=((n+1 : ℕ) : ℝ) :=
      sourceUnitLatitudeMap_norm_sq (by omega) u hu e he hr x.val (by rw [unit_norm];norm_num)
    dsimp [L]
    rw [sphereLinear,innerSL_apply_norm,fieldFeature_norm (by omega) c hcoeff _ hz,
      covariancePolynomial_center,covariancePolynomial_mixture,mul_one]
  have hR : ‖residual A‖ ≤ 1 := by
    rw [residual_eq_starProjection A hA]
    exact A.ker.starProjection_norm_le
  have hLiteral (g) : mixedLatitudeMaximum n μ Q r u e (Y g)=
      sourceAffineSupremum L (residual A) (lift A w) g := by
    unfold mixedLatitudeMaximum sourceAffineSupremum
    simp only [L,sphereLinear_apply]
    rfl
  have hMean : (∫ g,sourceAffineSupremum L (residual A) (lift A w) g ∂G)=
      (∫ J,mixedLatitudeMaximum n μ Q r u e J ∂P) := by
    have H := hLaw.integral_comp hM.aestronglyMeasurable
    simp only [Function.comp_def,hLiteral] at H
    exact H
  have HP := sourceAffineSupremum_centered_tail L hB hBound (residual A) hR (lift A w)
    (s := ((n+1 : ℕ) : ℝ)*t) (mul_nonneg hN.le ht)
  change G.real {g | (∫ z,sourceAffineSupremum L (residual A) (lift A w) z ∂G)+
    ((n+1 : ℕ) : ℝ)*t ≤ sourceAffineSupremum L (residual A) (lift A w) g} ≤ _ at HP
  rw [hMean] at HP
  have hEvent := hLaw.measureReal_eq (p := fun J =>
    (∫ K,mixedLatitudeMaximum n μ Q r u e K ∂P)+((n+1 : ℕ) : ℝ)*t ≤
      mixedLatitudeMaximum n μ Q r u e J) (measurableSet_le measurable_const hM)
  simp only [hLiteral] at hEvent
  rw [hEvent] at HP
  refine HP.trans_eq ?_
  dsimp [B]
  rw [Real.sq_sqrt (mul_nonneg hN.le hvar.le)]
  congr 1
  field_simp [hN.ne',hvar.ne']

/-- Actual mixed value/radial/zero-gradient conditional law, with uniform
marks and the genuine original covariance budget. -/
theorem actual_mixed_latitude_centered_tail {n : ℕ} (hn : 0 < n)
    (μ : FiniteMixture) {Q r : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (hr : r∈Ioo (0 : ℝ) 1) (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x,inner ℝ (e x) u=0) (e₀ k₀ : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    let P := mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu (scorePairEquiv (e₀,k₀))
    P.real {J | (∫ K,mixedLatitudeMaximum n μ Q r u e K ∂P)+((n+1 : ℕ) : ℝ)*t ≤
      mixedLatitudeMaximum n μ Q r u e J} ≤ Real.exp (-((n+1 : ℕ) : ℝ)*t^2/(2*μ.xi Q)) := by
  dsimp only
  apply actual_coefficient_kernel_latitude_centered_tail hn μ hQ hr u hu e he
  · exact center_joint_surjective (by omega) μ hQ hnp u hu _
      (tangentFrame_orthonormal u hu) (tangentFrame_tangent u hu)
  · exact ht

/-- The proper value-only law, including pure models, has the same true
original covariance budget. No redundant radial observation is inverted. -/
theorem actual_value_latitude_centered_tail {n : ℕ} (hn : 0 < n)
    (μ : FiniteMixture) {Q r : ℝ} (hQ : 0 < Q) (hr : r∈Ioo (0 : ℝ) 1)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x,inner ℝ (e x) u=0) (e₀ : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    let P := valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu e₀
    P.real {J | (∫ K,mixedLatitudeMaximum n μ Q r u e K ∂P)+((n+1 : ℕ) : ℝ)*t ≤
      mixedLatitudeMaximum n μ Q r u e J} ≤ Real.exp (-((n+1 : ℕ) : ℝ)*t^2/(2*μ.xi Q)) := by
  dsimp only
  apply actual_coefficient_kernel_latitude_centered_tail hn μ hQ hr u hu e he
  · exact center_valueTangent_surjective (by omega) μ hQ u hu _
      (tangentFrame_orthonormal u hu) (tangentFrame_tangent u hu)
  · exact ht

/-- At each fixed latitude, the actual internallyproved HS mean gives a
real exponential height upper, uniformly in center and every prescribed mark. -/
theorem eventual_actual_mixed_latitude_trial_upper_tail (μ : FiniteMixture) {Q r : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) (hr : r∈Ioo (0 : ℝ) 1)
    {L α s : ℝ} (hα : 0 ≤ α) (hs : s∈Icc (0 : ℝ) 1) (hb : 0 < L-α*(1-s))
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    ∀ᶠ n : ℕ in atTop,∀ (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
      (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (_he : ∀ x,inner ℝ (e x) u=0) (e₀ k₀ : ℝ),
      let P := mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu (scorePairEquiv (e₀,k₀))
      P.real {J | ((n+1 : ℕ) : ℝ)*(sourceConditionalMean μ Q e₀ k₀ r+
        functional (centeredFirst μ Q r) (centeredSecond μ Q r) L α s+ε)+
          ((n+1 : ℕ) : ℝ)*t ≤ mixedLatitudeMaximum n μ Q r u e J} ≤
        Real.exp (-((n+1 : ℕ) : ℝ)*t^2/(2*μ.xi Q)) := by
  have HM := eventual_actual_mixed_latitude_expected_maximum_upper μ hQ hnp hr hα hs hb hε
  filter_upwards [HM,eventually_gt_atTop (0 : ℕ)] with n hM hn
  intro u hu e he e₀ k₀
  dsimp only
  have : IsProbabilityMeasure (mixedConditionedLaw
      (centerCoefficients (mixtureCoefficients μ) Q) u hu (scorePairEquiv (e₀,k₀))) := by
    unfold mixedConditionedLaw
    infer_instance
  have hN : (0 : ℝ) < (n+1 : ℕ) := by positivity
  have hMean := (div_le_iff₀ hN).mp (hM u hu e he e₀ k₀)
  have H := actual_mixed_latitude_centered_tail hn μ hQ hnp hr u hu e he e₀ k₀ ht
  dsimp only at H
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans H
  intro J hJ
  change (∫ K,mixedLatitudeMaximum n μ Q r u e K
      ∂mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu (scorePairEquiv (e₀,k₀)))+
        ((n+1 : ℕ) : ℝ)*t ≤ mixedLatitudeMaximum n μ Q r u e J
  change ((n+1 : ℕ) : ℝ)*(sourceConditionalMean μ Q e₀ k₀ r+
    functional (centeredFirst μ Q r) (centeredSecond μ Q r) L α s+ε)+
      ((n+1 : ℕ) : ℝ)*t ≤ mixedLatitudeMaximum n μ Q r u e J at hJ
  nlinarith

end
end SlowEquilibration.SphericalParisiLatitudePosteriorTail
