-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalBandLaw
public import SlowEquilibration.CompactSphereCarrier
public import SlowEquilibration.SphericalTAPResidual
public import SlowEquilibration.SphericalResidualTemperatureLimits

@[expose] public section
/-! Genuine critical-point TAP-band pressure. This is the original
Hamiltonian integrated against the normalized transverse spherical law.
It is not a thermodynamic Parisi formula or a full-sphere existence theorem.
The actual posterior law and the internally proved residual RS theorem
give its expected physical pressure uniformly in prescribed marks. -/
namespace SlowEquilibration.SphericalTAPCriticalBand
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel SphericalGaussianJet WholeFieldRegression SphericalMarkedWindows
open SphericalTaylorRemainder SphericalTAPCertificate
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem compact_logPartition_add_const {K:Type*} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (ν:Measure K) [IsProbabilityMeasure ν]
    (β a:ℝ) (f:C(K,ℝ)) :
    ContinuousFieldPartition.logPartition ν β (f+ContinuousMap.const K a)=
      β*a+ContinuousFieldPartition.logPartition ν β f:=by
  unfold ContinuousFieldPartition.logPartition ContinuousFieldPartition.partition
  have he: (∫ x,Real.exp (β*(f x+a)) ∂ν)=Real.exp (β*a)*(∫ x,Real.exp (β*f x) ∂ν):=by
    simp_rw [mul_add,Real.exp_add]
    rw [integral_mul_const]
    ring
  change Real.log (∫ x,Real.exp (β*(f x+a)) ∂ν)=_
  have hp:0 < ∫ x,Real.exp (β*f x) ∂ν:=ContinuousFieldPartition.partition_pos ν β f
  rw [he,Real.log_mul (Real.exp_ne_zero _) hp.ne',Real.log_exp]

theorem compact_scaled_model_logPartition (n:ℕ) (hn:1 ≤ n) (θ:FiniteMixture)
    (β s:ℝ) (J:Disorder n θ.maxDegree) :
    ContinuousFieldPartition.logPartition (CompactSphereCarrier.law n) β
      (s • modelContinuousField (mixtureCoefficients θ)
        (fun x:CompactSphereCarrier.Carrier n=>x.val) continuous_subtype_val (euclideanDisorder J))=
      Real.log (mixturePartition θ (β*s) J):=by
  have he:s • modelContinuousField (mixtureCoefficients θ)
      (fun x:CompactSphereCarrier.Carrier n=>x.val) continuous_subtype_val (euclideanDisorder J)=
      ⟨fun x:CompactSphereCarrier.Carrier n=>s*field (mixtureCoefficients θ) J x.val,
        ((field_contDiff (mixtureCoefficients θ) J).continuous.comp continuous_subtype_val).const_mul s⟩:=by
    ext x
    rw [ContinuousMap.smul_apply,modelContinuousField_apply,valueObservation_actual]
    rfl
  rw [he,CompactSphereCarrier.logPartition_eq_sphere hn β
    (fun x=>s*field (mixtureCoefficients θ) J x)
    ((field_contDiff (mixtureCoefficients θ) J).continuous.const_mul s)]
  congr 1
  apply integral_congr_ae
  exact .of_forall (fun _=>congrArg Real.exp (by dsimp only [fieldOfMixture];ring))

/-- General full-process-law transport. Its law input is discharged by
the actual physical critical-band theorems in the source consumers below. -/
theorem critical_band_expected_logPartition_of_law
    {Ω:Type*} [MeasurableSpace Ω] (P:Measure Ω) [IsProbabilityMeasure P]
    (n:ℕ) (hn:1 ≤ n) (θ:FiniteMixture) {β s:ℝ} (hβ:0<β) (hs:0<s)
    (U:Ω→C(CompactSphereCarrier.Carrier n,ℝ)) (hU:Measurable U) (a:ℝ)
    (hLaw:P.map (fun J=>U J-ContinuousMap.const (CompactSphereCarrier.Carrier n) a)=
      (disorderLaw n θ.maxDegree).map (fun J=>s • modelContinuousField (mixtureCoefficients θ)
        (fun x:CompactSphereCarrier.Carrier n=>x.val) continuous_subtype_val (euclideanDisorder J))) :
    (∫ J,ContinuousFieldPartition.logPartition (CompactSphereCarrier.law n) β (U J) ∂P)=
      β*a+(∫ J,Real.log (mixturePartition θ (β*s) J) ∂disorderLaw n θ.maxDegree):=by
  let :IsProbabilityMeasure (CompactSphereCarrier.law n):=CompactSphereCarrier.law_probability hn
  let L:=ContinuousFieldPartition.logPartition (CompactSphereCarrier.law n) β
  let X:=fun J=>U J-ContinuousMap.const (CompactSphereCarrier.Carrier n) a
  let Y:=fun J:Disorder n θ.maxDegree=>s • modelContinuousField (mixtureCoefficients θ)
    (fun x:CompactSphereCarrier.Carrier n=>x.val) continuous_subtype_val (euclideanDisorder J)
  have hX:Measurable X:=hU.sub measurable_const
  have hY:Measurable Y:=((modelContinuousField (mixtureCoefficients θ)
    (fun x:CompactSphereCarrier.Carrier n=>x.val) continuous_subtype_val).continuous.measurable.comp
      (euclideanDisorder_measurable _ _)).const_smul s
  have hL:Measurable L:=ContinuousFieldPartition.logPartition_measurable _ _
  have hIntY:Integrable (fun J=>L (Y J)) (disorderLaw n θ.maxDegree):=
    (mixture_logPartition_integrable hn θ (mul_pos hβ hs)).congr
      (.of_forall (fun J=>(compact_scaled_model_logPartition n hn θ β s J).symm))
  have hMapped:Integrable L ((disorderLaw n θ.maxDegree).map Y):=
    (integrable_map_measure hL.aestronglyMeasurable hY.aemeasurable).mpr hIntY
  rw [←hLaw] at hMapped
  have hIntX:Integrable (fun J=>L (X J)) P:=
    (integrable_map_measure hL.aestronglyMeasurable hX.aemeasurable).mp hMapped
  have hMean:(∫ J,L (X J) ∂P)=∫ J,L (Y J) ∂disorderLaw n θ.maxDegree:=by
    rw [←integral_map hX.aemeasurable hL.aestronglyMeasurable,
      hLaw,integral_map hY.aemeasurable hL.aestronglyMeasurable]
  have hpoint (J:Ω):L (U J)=β*a+L (X J):=by
    have H:=compact_logPartition_add_const (CompactSphereCarrier.law n) β a (X J)
    simpa only [X,sub_add_cancel] using H
  rw [integral_congr_ae (.of_forall hpoint),integral_add (integrable_const _) hIntX,
    integral_const,probReal_univ,one_smul,hMean]
  congr 1
  apply integral_congr_ae
  exact .of_forall (fun J=>compact_scaled_model_logPartition n hn θ β s J)

def actualCriticalBandPressure (n:ℕ) (μ:FiniteMixture) (Q:ℝ)
    (u:Vector (n+1)) (e:Vector n→ₗᵢ[ℝ] Vector (n+1)) (β:ℝ)
    (J:Disorder (n+1) μ.maxDegree):ℝ:=
  ContinuousFieldPartition.logPartition (CompactSphereCarrier.law n) β
    (actualCriticalBandContinuousField n n μ Q u e
      (fun x:CompactSphereCarrier.Carrier n=>x.val) continuous_subtype_val (euclideanDisorder J))/(n+1:ℕ)

theorem actual_value_critical_band_expected_pressure_eq (n:ℕ) (hn:1 ≤ n)
    (μ:FiniteMixture) {Q β:ℝ} (hQ:Q∈Ioo (0:ℝ) 1) (hβ:0<β)
    (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ))
    (e:Vector n→ₗᵢ[ℝ] Vector (n+1)) (he:∀ y,inner ℝ (e y) u=0) (e₀:ℝ) :
    let θ:=μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)
    (∫ J,actualCriticalBandPressure n μ Q u e β J
      ∂valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu e₀)=
      β*e₀+(n:ℝ)/(n+1:ℕ)*quenchedPressure n θ (dimensionCorrectedTemperature β 1 n):=by
  dsimp only
  let θ:=μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)
  let P:=valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu e₀
  let :IsProbabilityMeasure P:=by unfold P valueConditionedLaw;infer_instance
  let U:=fun J:Disorder (n+1) μ.maxDegree=>actualCriticalBandContinuousField n n μ Q u e
    (fun x:CompactSphereCarrier.Carrier n=>x.val) continuous_subtype_val (euclideanDisorder J)
  have hU:Measurable U:=(actualCriticalBandContinuousField n n μ Q u e _ continuous_subtype_val).continuous.measurable.comp
    (euclideanDisorder_measurable _ _)
  have hS:0<Real.sqrt (((n+1:ℕ):ℝ)/(n:ℝ)):=by apply Real.sqrt_pos.mpr;positivity
  have H:=critical_band_expected_logPartition_of_law P n hn θ hβ hS U hU ((n+1:ℕ)*e₀)
    (actual_value_critical_band_continuous_law n n (by omega) μ hQ u hu e he _ continuous_subtype_val e₀)
  unfold actualCriticalBandPressure
  rw [integral_div,H]
  unfold quenchedPressure dimensionCorrectedTemperature
  dsimp only [θ]
  field_simp [show (n:ℝ)≠0 by exact_mod_cast (show n≠0 by omega)]

theorem actual_mixed_critical_band_expected_pressure_eq (n:ℕ) (hn:1 ≤ n)
    (μ:FiniteMixture) {Q β:ℝ} (hQ:Q∈Ioo (0:ℝ) 1) (hβ:0<β) (hnp:μ.minDegree<μ.maxDegree)
    (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ))
    (e:Vector n→ₗᵢ[ℝ] Vector (n+1)) (he:∀ y,inner ℝ (e y) u=0)
    (b:EuclideanSpace ℝ (Fin 2)) :
    let θ:=μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)
    (∫ J,actualCriticalBandPressure n μ Q u e β J
      ∂mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b)=
      β*b 0+(n:ℝ)/(n+1:ℕ)*quenchedPressure n θ (dimensionCorrectedTemperature β 1 n):=by
  dsimp only
  let θ:=μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)
  let P:=mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b
  let :IsProbabilityMeasure P:=by unfold P mixedConditionedLaw;infer_instance
  let U:=fun J:Disorder (n+1) μ.maxDegree=>actualCriticalBandContinuousField n n μ Q u e
    (fun x:CompactSphereCarrier.Carrier n=>x.val) continuous_subtype_val (euclideanDisorder J)
  have hU:Measurable U:=(actualCriticalBandContinuousField n n μ Q u e _ continuous_subtype_val).continuous.measurable.comp
    (euclideanDisorder_measurable _ _)
  have hS:0<Real.sqrt (((n+1:ℕ):ℝ)/(n:ℝ)):=by apply Real.sqrt_pos.mpr;positivity
  have H:=critical_band_expected_logPartition_of_law P n hn θ hβ hS U hU ((n+1:ℕ)*b 0)
    (actual_mixed_critical_band_continuous_law n n (by omega) μ hQ hnp u hu e he _ continuous_subtype_val b)
  unfold actualCriticalBandPressure
  rw [integral_div,H]
  unfold quenchedPressure dimensionCorrectedTemperature
  dsimp only [θ]
  field_simp [show (n:ℝ)≠0 by exact_mod_cast (show n≠0 by omega)]

/-- The actual value-only critical band has its residual RS expected
pressure limit, uniformly in all true centers, tangent frames and marks.
The strict certificate internally proves the residual RS condition. -/
theorem eventual_actual_value_critical_band_pressure (μ:FiniteMixture)
    {β x Q ε:ℝ} (h:Certificate μ β x Q) (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop,∀ (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ))
      (e:Vector n→ₗᵢ[ℝ] Vector (n+1)) (_he:∀ y,inner ℝ (e y) u=0) (e₀:ℝ),
      |(∫ J,actualCriticalBandPressure n μ Q u e β J
        ∂valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu e₀)-
          (β*e₀+β^2*(μ.xi 1-μ.xi Q-(1-Q)*μ.xi1 Q)/2)|<ε:=by
  let θ:=μ.taylorResidual h.overlap_range.1 (sub_pos.mpr h.overlap_range.2)
  let F:=β^2*(μ.xi 1-μ.xi Q-(1-Q)*μ.xi1 Q)/2
  have H:=quenchedPressure_tendsto_dimensionCorrected_per_ambient θ h.beta_pos.le 1
    (SphericalTAPResidual.residual_physical_pressure h)
  have ht:∀ᶠ n:ℕ in atTop,
      |(n:ℝ)/(n+1:ℕ)*quenchedPressure n θ (dimensionCorrectedTemperature β 1 n)-F|<ε:=by
    simpa only [Metric.mem_ball,Real.dist_eq] using H.eventually (Metric.ball_mem_nhds F hε)
  filter_upwards [ht,eventually_ge_atTop (1:ℕ)] with n hn hdim
  intro u hu e he e₀
  rw [actual_value_critical_band_expected_pressure_eq n hdim μ h.overlap_range h.beta_pos u hu e he e₀]
  have hCancel:β*e₀+(n:ℝ)/(n+1:ℕ)*quenchedPressure n θ (dimensionCorrectedTemperature β 1 n)-
      (β*e₀+F)=(n:ℝ)/(n+1:ℕ)*quenchedPressure n θ (dimensionCorrectedTemperature β 1 n)-F:=by ring
  change |β*e₀+(n:ℝ)/(n+1:ℕ)*quenchedPressure n θ (dimensionCorrectedTemperature β 1 n)-(β*e₀+F)|<ε
  rw [hCancel]
  exact hn

/-- The same true expected-pressure conclusion for the literal mixed
critical posterior, independent of its radial score mark. -/
theorem eventual_actual_mixed_critical_band_pressure (μ:FiniteMixture)
    {β x Q ε:ℝ} (h:Certificate μ β x Q) (hnp:μ.minDegree<μ.maxDegree) (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop,∀ (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ))
      (e:Vector n→ₗᵢ[ℝ] Vector (n+1)) (_he:∀ y,inner ℝ (e y) u=0)
      (b:EuclideanSpace ℝ (Fin 2)),
      |(∫ J,actualCriticalBandPressure n μ Q u e β J
        ∂mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b)-
          (β*b 0+β^2*(μ.xi 1-μ.xi Q-(1-Q)*μ.xi1 Q)/2)|<ε:=by
  let θ:=μ.taylorResidual h.overlap_range.1 (sub_pos.mpr h.overlap_range.2)
  let F:=β^2*(μ.xi 1-μ.xi Q-(1-Q)*μ.xi1 Q)/2
  have H:=quenchedPressure_tendsto_dimensionCorrected_per_ambient θ h.beta_pos.le 1
    (SphericalTAPResidual.residual_physical_pressure h)
  have ht:∀ᶠ n:ℕ in atTop,
      |(n:ℝ)/(n+1:ℕ)*quenchedPressure n θ (dimensionCorrectedTemperature β 1 n)-F|<ε:=by
    simpa only [Metric.mem_ball,Real.dist_eq] using H.eventually (Metric.ball_mem_nhds F hε)
  filter_upwards [ht,eventually_ge_atTop (1:ℕ)] with n hn hdim
  intro u hu e he b
  rw [actual_mixed_critical_band_expected_pressure_eq n hdim μ h.overlap_range h.beta_pos hnp u hu e he b]
  have hCancel:β*b 0+(n:ℝ)/(n+1:ℕ)*quenchedPressure n θ (dimensionCorrectedTemperature β 1 n)-
      (β*b 0+F)=(n:ℝ)/(n+1:ℕ)*quenchedPressure n θ (dimensionCorrectedTemperature β 1 n)-F:=by ring
  change |β*b 0+(n:ℝ)/(n+1:ℕ)*quenchedPressure n θ (dimensionCorrectedTemperature β 1 n)-(β*b 0+F)|<ε
  rw [hCancel]
  exact hn

end
end SlowEquilibration.SphericalTAPCriticalBand
