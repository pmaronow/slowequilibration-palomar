-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiLatitudeGroundAuxiliary
public import SlowEquilibration.SphericalParisiContinuousMaximum

@[expose] public section

/-! Genuine expected maximum of a physical critical-conditioned latitude.
The actual mixed posterior whole C(K)-law, its deterministic mean, the
independent degree-zero/one/higher auxiliary tensor model and exact n+1/n
physical compensation are used. The HS upper and expected maximum bound
are derived internally and are uniform in center and prescribed marks. -/

namespace SlowEquilibration.SphericalParisiLatitudePosteriorGround
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel FiniteTensorMixtureMaximum PureTensorJetBounds
open SphericalGaussianJet WholeFieldRegression SphericalPosteriorMaps SphericalSequentialRegression
open SphericalMarkedWindows SphericalTaylorRemainder GaussianContinuousFieldLaw
open SphericalCriticalLatitude SphericalParisiConditionedLatitudeCovariance LatitudeGroundTrial
open SphericalParisiLatitudeGroundAuxiliary SphericalParisiGroundRSUpper
open SphericalParisiContinuousMaximum
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def unitLatitudePoints {n : ℕ} (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (r : ℝ) : UnitSphere n → Vector (n+1) :=
  fun x => sourceUnitLatitudeMap u e r x.val

theorem unitLatitudePoints_continuous {n : ℕ} (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (r : ℝ) : Continuous (unitLatitudePoints u e r) :=
  (sourceUnitLatitudeMap_continuous u e r).comp continuous_subtype_val

def mixedLatitudeContinuousField (n : ℕ) (μ : FiniteMixture) (Q r : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) :
    EuclideanDisorder (n+1) μ.maxDegree →L[ℝ] C(UnitSphere n,ℝ) :=
  criticalContinuousField n μ Q (unitLatitudePoints u e r) (unitLatitudePoints_continuous u e r)

/-- Literal original physical field supremum on the actual unit-transverse
latitude parameterization, before any regression or auxiliary-law rewrite. -/
def mixedLatitudeMaximum (n : ℕ) (μ : FiniteMixture) (Q r : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (J : Disorder (n+1) μ.maxDegree) : ℝ :=
  ⨆ x : UnitSphere n,field (centerCoefficients (mixtureCoefficients μ) Q) J
    (sourceUnitLatitudeMap u e r x.val)

theorem mixedLatitudeMaximum_eq_maximum {n : ℕ} (hn : 0 < n)
    (μ : FiniteMixture) (Q r : ℝ) (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (J : Disorder (n+1) μ.maxDegree) :
    mixedLatitudeMaximum n μ Q r u e J=
      maximum (mixedLatitudeContinuousField n μ Q r u e (euclideanDisorder J)) := by
  let : NeZero n := ⟨hn.ne'⟩
  unfold mixedLatitudeMaximum maximum mixedLatitudeContinuousField criticalContinuousField
  congr 1
  funext x
  simp only [modelContinuousField_apply,valueObservation,flatJetCLM_apply,jet,
    iteratedFDeriv_zero_apply,unpack_euclideanDisorder]
  rfl

/-- Samplewise actual auxiliary supremum at physical dimension n+1. -/
theorem actual_auxiliary_continuous_maximum {n : ℕ} (hn : 0 < n)
    (μ : FiniteMixture) (Q r : ℝ)
    (g : EuclideanSpace ℝ (Coordinate n (sourceAuxiliaryDegree μ Q r))) :
    maximum (auxiliaryContinuousField μ Q r (n+1) n
      (fun x : UnitSphere n => x.val) continuous_subtype_val g)=
      physicalAuxiliaryMaximum μ Q r n g := by
  let : NeZero n := ⟨hn.ne'⟩
  let f : C(UnitSphere n,ℝ) :=
    ⟨fun x => inner ℝ (feature (sourceAuxiliaryDegree μ Q r) (sourceAuxiliaryCoefficient μ Q r) x.val) g,
      (((feature_continuous _ _).comp continuous_subtype_val).inner continuous_const)⟩
  have he : auxiliaryContinuousField μ Q r (n+1) n
      (fun x : UnitSphere n => x.val) continuous_subtype_val g=
        Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)) • f := by
    ext x
    simp only [auxiliaryContinuousField,featureContinuousField_apply,innerSL_apply_apply,
      real_inner_smul_left,ContinuousMap.smul_apply,smul_eq_mul]
    rfl
  rw [he,maximum_nonneg_smul f (Real.sqrt_nonneg _)]
  rfl

/-- Exact expected full posterior latitude maximum, from the genuine
continuous field-law transport, including its nonzero physical mark mean. -/
theorem actual_mixed_latitude_expected_maximum_eq {n : ℕ} (hn : 0 < n)
    (μ : FiniteMixture) {Q r : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (hr : r∈Ioo (0 : ℝ) 1) (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x,inner ℝ (e x) u=0) (e₀ k₀ : ℝ) :
    (∫ J,mixedLatitudeMaximum n μ Q r u e J
      ∂mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu (scorePairEquiv (e₀,k₀)))=
    ((n+1 : ℕ) : ℝ)*sourceConditionalMean μ Q e₀ k₀ r+
      (∫ g,physicalAuxiliaryMaximum μ Q r n g
        ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate n (sourceAuxiliaryDegree μ Q r))) := by
  classical
  let : NeZero n := ⟨hn.ne'⟩
  let P := mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu (scorePairEquiv (e₀,k₀))
  let G := SYK.standardGaussianMeasureOnEuclidean (Coordinate n (sourceAuxiliaryDegree μ Q r))
  let U := fun J : Disorder (n+1) μ.maxDegree =>
    mixedLatitudeContinuousField n μ Q r u e (euclideanDisorder J)
  let a : ℝ := ((n+1 : ℕ) : ℝ)*sourceConditionalMean μ Q e₀ k₀ r
  let X := fun J : Disorder (n+1) μ.maxDegree => U J-ContinuousMap.const (UnitSphere n) a
  let Y := auxiliaryContinuousField μ Q r (n+1) n (fun x : UnitSphere n => x.val) continuous_subtype_val
  have hU : Measurable U := (mixedLatitudeContinuousField n μ Q r u e).continuous.measurable.comp
    (SphericalTaylorRemainder.euclideanDisorder_measurable _ _)
  have hX : Measurable X := hU.sub measurable_const
  have hY : Measurable Y := Y.continuous.measurable
  have hG : stdGaussian (EuclideanSpace ℝ (Coordinate n (sourceAuxiliaryDegree μ Q r)))=G := by
    dsimp [G]
    rw [SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian]
  have hLaw : P.map X=G.map Y := by
    have H := actual_critical_latitude_auxiliary_continuous_law μ hQ hnp hr n n hn
      u hu e he (fun x : UnitSphere n => x.val) continuous_subtype_val e₀ k₀
    dsimp only at H
    rw [hG] at H
    exact H
  let W := fun g => Y g+ContinuousMap.const (UnitSphere n) a
  have hW : Measurable W := hY.add measurable_const
  have hAdd : Measurable (fun f : C(UnitSphere n,ℝ) => f+ContinuousMap.const (UnitSphere n) a) :=
    measurable_id.add measurable_const
  have hFullLaw : P.map U=G.map W := by
    have H := congrArg (fun Λ : Measure C(UnitSphere n,ℝ) =>
      Λ.map (fun f => f+ContinuousMap.const (UnitSphere n) a)) hLaw
    rw [Measure.map_map hAdd hX,Measure.map_map hAdd hY] at H
    simpa only [Function.comp_def,X,W,sub_add_cancel] using H
  have hMean := maximum_integral_eq_of_field_law P G U W hU hW hFullLaw
  have hYmax (g) : maximum (Y g)=physicalAuxiliaryMaximum μ Q r n g :=
    actual_auxiliary_continuous_maximum hn μ Q r g
  have hi : Integrable (physicalAuxiliaryMaximum μ Q r n) G := by
    exact (actualMaximum_integrable hn (sourceAuxiliaryDegree μ Q r)
      (sourceAuxiliaryCoefficient μ Q r)).const_mul _
  have hWmax (g) : maximum (W g)=physicalAuxiliaryMaximum μ Q r n g+a := by
    rw [show W g=Y g+ContinuousMap.const (UnitSphere n) a from rfl,maximum_add_const,hYmax]
  rw [integral_congr_ae (.of_forall hWmax),integral_add hi (integrable_const a)] at hMean
  simp only [integral_const,probReal_univ,one_smul] at hMean
  have hUmax (J) : maximum (U J)=mixedLatitudeMaximum n μ Q r u e J :=
    (mixedLatitudeMaximum_eq_maximum hn μ Q r u e J).symm
  rw [integral_congr_ae (.of_forall hUmax)] at hMean
  exact hMean.trans (by ring)

/-- The actual posterior expected upper is uniform in the prescribed
marks, center, and tangent isometry; the dimension threshold depends only
on the fixed latitude covariance, admissible trial and positive slack. -/
theorem eventual_actual_mixed_latitude_expected_maximum_upper (μ : FiniteMixture) {Q r : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) (hr : r∈Ioo (0 : ℝ) 1)
    {L α s : ℝ} (hα : 0 ≤ α) (hs : s∈Icc (0 : ℝ) 1) (hb : 0 < L-α*(1-s))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,∀ (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
      (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (_he : ∀ x,inner ℝ (e x) u=0) (e₀ k₀ : ℝ),
      (∫ J,mixedLatitudeMaximum n μ Q r u e J
        ∂mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu (scorePairEquiv (e₀,k₀)))/
          ((n+1 : ℕ) : ℝ) ≤
      sourceConditionalMean μ Q e₀ k₀ r+functional (centeredFirst μ Q r) (centeredSecond μ Q r) L α s+ε := by
  have H := eventual_actual_physical_auxiliary_ground_upper μ hQ hnp hr hα hs hb hε
  filter_upwards [H,eventually_gt_atTop (0 : ℕ)] with n hH hn
  intro u hu e he e₀ k₀
  rw [actual_mixed_latitude_expected_maximum_eq hn μ hQ hnp hr u hu e he e₀ k₀]
  have hN : (0 : ℝ) < (n+1 : ℕ) := by positivity
  have heq : (((n+1 : ℕ) : ℝ)*sourceConditionalMean μ Q e₀ k₀ r+
      (∫ g,physicalAuxiliaryMaximum μ Q r n g
        ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate n (sourceAuxiliaryDegree μ Q r))))/
          ((n+1 : ℕ) : ℝ)=sourceConditionalMean μ Q e₀ k₀ r+
      ((∫ g,physicalAuxiliaryMaximum μ Q r n g
        ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate n (sourceAuxiliaryDegree μ Q r)))/
          ((n+1 : ℕ) : ℝ)) := by field_simp
  rw [heq]
  linarith

end
end SlowEquilibration.SphericalParisiLatitudePosteriorGround
