-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiLatitudePosteriorTail
public import SlowEquilibration.SphericalParisiFiniteMixtureGroundBridge
public import SlowEquilibration.LatitudeGroundPureTrial

@[expose] public section

/-! Proper-pure fixed-latitude physical expectedmaximum and exponential
height upper. Only value and zero tangent gradient are conditioned; the
redundant radial observation and singular score inverse are absent. The
true whole C(K)-law is transported to the actual Taylor residual mixture,
whose HS upper and physical n+1/n normalization are internally proved. -/

namespace SlowEquilibration.SphericalParisiPureLatitudePosteriorGround
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet PureTensorJetBounds SphericalMarkedWindows SphericalCriticalLatitude
open SphericalTaylorRemainder SphericalParisiContinuousMaximum SphericalParisiLatitudePosteriorGround
open SphericalParisiLatitudePosteriorTail SphericalParisiFiniteMixtureGroundBridge
open LatitudeGroundTrial SphericalParisiConditionedLatitudeCovariance
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Exact actual proper-pure posterior expectedmaximum, with the physical
mark mean Ne*r^p and the genuine independent Taylor residual field. -/
theorem actual_pure_latitude_expected_maximum_eq {n : ℕ} (hn : 0 < n)
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) {Q r : ℝ}
    (hQ : 0 < Q) (hr : r∈Ioo (0 : ℝ) 1)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x,inner ℝ (e x) u=0) (e₀ : ℝ) :
    let μ := FiniteMixture.pure p hp c hc
    let θ := pureLatitudeResidual p hp c hc hQ hr
    (∫ J,mixedLatitudeMaximum n μ Q r u e J
      ∂valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu e₀)=
    ((n+1 : ℕ) : ℝ)*e₀*r^p+
      (∫ g,maximum (physicalResidualContinuousField θ (n+1) n
        (fun x : UnitSphere n => x.val) continuous_subtype_val g)
        ∂stdGaussian (EuclideanDisorder n θ.maxDegree)) := by
  classical
  dsimp only
  let : NeZero n := ⟨hn.ne'⟩
  let μ := FiniteMixture.pure p hp c hc
  let θ := pureLatitudeResidual p hp c hc hQ hr
  let P := valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu e₀
  let G := stdGaussian (EuclideanDisorder n θ.maxDegree)
  let U := fun J : Disorder (n+1) μ.maxDegree => mixedLatitudeContinuousField n μ Q r u e (euclideanDisorder J)
  let a : ℝ := ((n+1 : ℕ) : ℝ)*e₀*r^p
  let X := fun J : Disorder (n+1) μ.maxDegree => U J-ContinuousMap.const (UnitSphere n) a
  let Y := physicalResidualContinuousField θ (n+1) n (fun x : UnitSphere n => x.val) continuous_subtype_val
  have hU : Measurable U := (mixedLatitudeContinuousField n μ Q r u e).continuous.measurable.comp
    (SphericalTaylorRemainder.euclideanDisorder_measurable _ _)
  have hX : Measurable X := hU.sub measurable_const
  have hY : Measurable Y := Y.continuous.measurable
  have hLaw : P.map X=G.map Y := by
    have H := actual_pure_critical_latitude_continuous_law p hp c hc hQ hr n n hn
      u hu e he (fun x : UnitSphere n => x.val) continuous_subtype_val e₀
    dsimp only at H
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
  have hYint : Integrable (fun g => maximum (Y g)) G := by
    have hG : stdGaussian (EuclideanSpace ℝ (FiniteTensorMixtureMaximum.Coordinate n (tensorDegree θ)))=
        SYK.standardGaussianMeasureOnEuclidean (FiniteTensorMixtureMaximum.Coordinate n (tensorDegree θ)) := by
      rw [SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian]
    have hModel := physicalResidualContinuousField_tensor_law θ (n+1) n hn
      (fun x : UnitSphere n => x.val) continuous_subtype_val
    let Z := finiteMixtureTensorContinuousField θ (n+1) n (fun x : UnitSphere n => x.val) continuous_subtype_val
    have hZint : Integrable (fun g => maximum (Z g))
        (stdGaussian (EuclideanSpace ℝ (FiniteTensorMixtureMaximum.Coordinate n (tensorDegree θ)))) := by
      rw [hG]
      have H := (SphericalParisiGroundRSUpper.actualMaximum_integrable hn
        (tensorDegree θ) (tensorCoefficient θ)).const_mul (Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)))
      exact H.congr (.of_forall (fun g => (finiteMixtureTensorContinuousField_maximum θ (n+1) n hn g).symm))
    have hMapped : Integrable (maximum (K := UnitSphere n))
        ((stdGaussian (EuclideanSpace ℝ (FiniteTensorMixtureMaximum.Coordinate n (tensorDegree θ)))).map Z) :=
      (integrable_map_measure maximum_measurable.aestronglyMeasurable Z.continuous.measurable.aemeasurable).mpr hZint
    rw [← hModel] at hMapped
    exact (integrable_map_measure maximum_measurable.aestronglyMeasurable Y.continuous.measurable.aemeasurable).mp hMapped
  have hWmax (g) : maximum (W g)=maximum (Y g)+a := maximum_add_const (Y g) a
  rw [integral_congr_ae (.of_forall hWmax),integral_add hYint (integrable_const a)] at hMean
  simp only [integral_const,probReal_univ,one_smul] at hMean
  have hUmax (J) : maximum (U J)=mixedLatitudeMaximum n μ Q r u e J :=
    (mixedLatitudeMaximum_eq_maximum hn μ Q r u e J).symm
  rw [integral_congr_ae (.of_forall hUmax)] at hMean
  exact hMean.trans (by ring)

/-- The actual proper-pure expectedmaximum is bounded by every admissible
source trial, uniformly in sphere center, tangent isometry and value mark. -/
theorem eventual_actual_pure_latitude_expected_maximum_upper
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) {Q r : ℝ}
    (hQ : 0 < Q) (hr : r∈Ioo (0 : ℝ) 1)
    {L α s : ℝ} (hα : 0 ≤ α) (hs : s∈Icc (0 : ℝ) 1) (hb : 0 < L-α*(1-s))
    {ε : ℝ} (hε : 0 < ε) :
    let μ := FiniteMixture.pure p hp c hc
    ∀ᶠ n : ℕ in atTop,∀ (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
      (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (_he : ∀ x,inner ℝ (e x) u=0) (e₀ : ℝ),
      (∫ J,mixedLatitudeMaximum n μ Q r u e J
        ∂valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu e₀)/((n+1 : ℕ) : ℝ) ≤
        e₀*r^p+functional (centeredFirst μ Q r) (centeredSecond μ Q r) L α s+ε := by
  dsimp only
  let θ := pureLatitudeResidual p hp c hc hQ hr
  have H := eventual_physical_finiteMixture_ground_upper θ hα hs hb hε
  obtain ⟨hfirst,hsecond⟩ := pure_residual_trial_derivatives p hp c hc hQ hr
  rw [hfirst,hsecond] at H
  filter_upwards [H,eventually_gt_atTop (0 : ℕ)] with n hH hn
  intro u hu e he e₀
  rw [actual_pure_latitude_expected_maximum_eq hn p hp c hc hQ hr u hu e he e₀]
  have hN : (0 : ℝ) < (n+1 : ℕ) := by positivity
  have heq : (((n+1 : ℕ) : ℝ)*e₀*r^p+
      (∫ g,maximum (physicalResidualContinuousField θ (n+1) n
        (fun x : UnitSphere n => x.val) continuous_subtype_val g)
        ∂stdGaussian (EuclideanDisorder n θ.maxDegree)))/((n+1 : ℕ) : ℝ)=
        e₀*r^p+(∫ g,maximum (physicalResidualContinuousField θ (n+1) n
          (fun x : UnitSphere n => x.val) continuous_subtype_val g)
          ∂stdGaussian (EuclideanDisorder n θ.maxDegree))/((n+1 : ℕ) : ℝ) := by field_simp
  rw [heq]
  linarith

/-- At every fixed latitude, the proper-pure original conditional height
has a real exponential upper from the internallyproved HS mean. -/
theorem eventual_actual_pure_latitude_trial_upper_tail
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) {Q r : ℝ}
    (hQ : 0 < Q) (hr : r∈Ioo (0 : ℝ) 1)
    {L α s : ℝ} (hα : 0 ≤ α) (hs : s∈Icc (0 : ℝ) 1) (hb : 0 < L-α*(1-s))
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    let μ := FiniteMixture.pure p hp c hc
    ∀ᶠ n : ℕ in atTop,∀ (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
      (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (_he : ∀ x,inner ℝ (e x) u=0) (e₀ : ℝ),
      let P := valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu e₀
      P.real {J | ((n+1 : ℕ) : ℝ)*(e₀*r^p+
        functional (centeredFirst μ Q r) (centeredSecond μ Q r) L α s+ε)+
          ((n+1 : ℕ) : ℝ)*t ≤ mixedLatitudeMaximum n μ Q r u e J} ≤
        Real.exp (-((n+1 : ℕ) : ℝ)*t^2/(2*μ.xi Q)) := by
  dsimp only
  let μ := FiniteMixture.pure p hp c hc
  have HM := eventual_actual_pure_latitude_expected_maximum_upper p hp c hc hQ hr hα hs hb hε
  dsimp only at HM
  filter_upwards [HM,eventually_gt_atTop (0 : ℕ)] with n hM hn
  intro u hu e he e₀
  have : IsProbabilityMeasure (valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu e₀) := by
    unfold valueConditionedLaw
    infer_instance
  have hN : (0 : ℝ) < (n+1 : ℕ) := by positivity
  have hMean := (div_le_iff₀ hN).mp (hM u hu e he e₀)
  have H := actual_value_latitude_centered_tail hn μ hQ hr u hu e he e₀ ht
  dsimp only at H
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans H
  intro J hJ
  change (∫ K,mixedLatitudeMaximum n μ Q r u e K
      ∂valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu e₀)+
        ((n+1 : ℕ) : ℝ)*t ≤ mixedLatitudeMaximum n μ Q r u e J
  change ((n+1 : ℕ) : ℝ)*(e₀*r^p+
    functional (centeredFirst μ Q r) (centeredSecond μ Q r) L α s+ε)+
      ((n+1 : ℕ) : ℝ)*t ≤ mixedLatitudeMaximum n μ Q r u e J at hJ
  nlinarith

end
end SlowEquilibration.SphericalParisiPureLatitudePosteriorGround
