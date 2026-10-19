-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPResidualDimensionCorrectedTightness

@[expose] public section
/-! Literal normalized partition of the original exact critical TAP band.
Its complete scalar law is the actual dimension-corrected residual model;
the source lower-tail conclusion follows from a raw one-step certificate,
with neither a Parisi formula nor a normalized-tightness premise. -/
namespace SlowEquilibration.SphericalTAPCriticalBand
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel SphericalGaussianJet WholeFieldRegression SphericalMarkedWindows
open SphericalTaylorRemainder SphericalTAPCertificate
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def actualCriticalResidualNormalizedPartition (n:ℕ) (μ:FiniteMixture) {Q:ℝ}
    (hQ:Q∈Ioo (0:ℝ) 1) (u:Vector (n+1)) (e:Vector n→ₗᵢ[ℝ] Vector (n+1))
    (β e₀:ℝ) (J:Disorder (n+1) μ.maxDegree):ℝ:=
  Real.exp (ContinuousFieldPartition.logPartition (CompactSphereCarrier.law n) β
    (actualCriticalBandContinuousField n n μ Q u e
      (fun x:CompactSphereCarrier.Carrier n=>x.val) continuous_subtype_val (euclideanDisorder J)-
        ContinuousMap.const (CompactSphereCarrier.Carrier n) ((n+1:ℕ)*e₀))-
    ((n+1:ℕ):ℝ)*β^2*(μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)).xi 1/2)

theorem actualCriticalResidualNormalizedPartition_measurable (n:ℕ) (hn:1 ≤ n)
    (μ:FiniteMixture) {Q:ℝ} (hQ:Q∈Ioo (0:ℝ) 1)
    (u:Vector (n+1)) (e:Vector n→ₗᵢ[ℝ] Vector (n+1)) (β e₀:ℝ) :
    Measurable (actualCriticalResidualNormalizedPartition n μ hQ u e β e₀):=by
  let :IsProbabilityMeasure (CompactSphereCarrier.law n):=CompactSphereCarrier.law_probability hn
  unfold actualCriticalResidualNormalizedPartition
  apply Real.measurable_exp.comp
  apply Measurable.sub_const
  apply (ContinuousFieldPartition.logPartition_measurable _ _).comp
  exact ((actualCriticalBandContinuousField n n μ Q u e _ continuous_subtype_val).continuous.measurable.comp
    (euclideanDisorder_measurable _ _)).sub measurable_const

/-- The observable is exactly the source normalized positive partition,
not a substitute pressure event. -/
theorem actualCriticalResidualNormalizedPartition_eq_partition (n:ℕ) (hn:1 ≤ n)
    (μ:FiniteMixture) {Q:ℝ} (hQ:Q∈Ioo (0:ℝ) 1)
    (u:Vector (n+1)) (e:Vector n→ₗᵢ[ℝ] Vector (n+1)) (β e₀:ℝ)
    (J:Disorder (n+1) μ.maxDegree) :
    actualCriticalResidualNormalizedPartition n μ hQ u e β e₀ J=
      Real.exp (-((n+1:ℕ):ℝ)*β^2*(μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)).xi 1/2)*
        ContinuousFieldPartition.partition (CompactSphereCarrier.law n) β
          (actualCriticalBandContinuousField n n μ Q u e _ continuous_subtype_val (euclideanDisorder J)-
            ContinuousMap.const (CompactSphereCarrier.Carrier n) ((n+1:ℕ)*e₀)):=by
  let :IsProbabilityMeasure (CompactSphereCarrier.law n):=CompactSphereCarrier.law_probability hn
  unfold actualCriticalResidualNormalizedPartition ContinuousFieldPartition.logPartition
  rw [Real.exp_sub,Real.exp_log (ContinuousFieldPartition.partition_pos _ _ _),div_eq_mul_inv,←Real.exp_neg]
  simp only [neg_div,neg_mul,mul_comm]

theorem physicalResidualNormalizedPartition_measurable (n:ℕ) (θ:FiniteMixture) (β:ℝ) :
    Measurable (physicalResidualNormalizedPartition n θ β):=by
  unfold physicalResidualNormalizedPartition mixturePartition fieldOfMixture
  exact measurable_const.mul (partition_measurable (mixtureCoefficients θ) _)

/-- Scalar normalized-partition transport from a full process law. The
actual physical source laws discharge this reduction in both consumers. -/
theorem critical_residual_partition_law_of_field_law
    {Ω:Type*} [MeasurableSpace Ω] (P:Measure Ω) (n:ℕ) (hn:1 ≤ n) (θ:FiniteMixture)
    (β:ℝ) (U:Ω→C(CompactSphereCarrier.Carrier n,ℝ)) (hU:Measurable U) (a:ℝ)
    (hLaw:P.map (fun J=>U J-ContinuousMap.const (CompactSphereCarrier.Carrier n) a)=
      (disorderLaw n θ.maxDegree).map (fun J=>Real.sqrt (((n+1:ℕ):ℝ)/(n:ℝ)) •
        modelContinuousField (mixtureCoefficients θ) (fun x:CompactSphereCarrier.Carrier n=>x.val)
          continuous_subtype_val (euclideanDisorder J))) :
    P.map (fun J=>Real.exp (ContinuousFieldPartition.logPartition (CompactSphereCarrier.law n) β
      (U J-ContinuousMap.const (CompactSphereCarrier.Carrier n) a)-((n+1:ℕ):ℝ)*β^2*θ.xi 1/2))=
      (disorderLaw n θ.maxDegree).map (physicalResidualNormalizedPartition n θ β):=by
  let :IsProbabilityMeasure (CompactSphereCarrier.law n):=CompactSphereCarrier.law_probability hn
  let Φ:=fun f:C(CompactSphereCarrier.Carrier n,ℝ)=>Real.exp
    (ContinuousFieldPartition.logPartition (CompactSphereCarrier.law n) β f-((n+1:ℕ):ℝ)*β^2*θ.xi 1/2)
  have hΦ:Measurable Φ:=Real.measurable_exp.comp ((ContinuousFieldPartition.logPartition_measurable _ _).sub_const _)
  have hX:Measurable (fun J=>U J-ContinuousMap.const (CompactSphereCarrier.Carrier n) a):=
    hU.sub measurable_const
  have hBase:Measurable (fun J:Disorder n θ.maxDegree=>
      modelContinuousField (mixtureCoefficients θ)
        (fun x:CompactSphereCarrier.Carrier n=>x.val) continuous_subtype_val
        (euclideanDisorder J)):=
    (modelContinuousField (mixtureCoefficients θ) _ continuous_subtype_val).continuous.measurable.comp
      (euclideanDisorder_measurable n θ.maxDegree)
  have hY:Measurable (fun J:Disorder n θ.maxDegree=>Real.sqrt (((n+1:ℕ):ℝ)/(n:ℝ)) •
      modelContinuousField (mixtureCoefficients θ) (fun x:CompactSphereCarrier.Carrier n=>x.val)
        continuous_subtype_val (euclideanDisorder J)):=by
    have hScale:Continuous (fun f:C(CompactSphereCarrier.Carrier n,ℝ)=>
        Real.sqrt (((n+1:ℕ):ℝ)/(n:ℝ)) • f):=
      (continuous_const : Continuous (fun _ : C(CompactSphereCarrier.Carrier n,ℝ) =>
        (Real.sqrt (((n+1:ℕ):ℝ)/(n:ℝ)) : ℝ))).smul
        (continuous_id : Continuous (fun f:C(CompactSphereCarrier.Carrier n,ℝ)=>f))
    exact hScale.measurable.comp hBase
  have H:=congrArg (fun ν:Measure C(CompactSphereCarrier.Carrier n,ℝ)=>ν.map Φ) hLaw
  rw [Measure.map_map hΦ hX,Measure.map_map hΦ hY] at H
  refine H.trans ?_
  congr 1
  funext J
  dsimp only [Function.comp_def,Φ]
  rw [compact_scaled_model_logPartition n hn θ β _ J]
  unfold physicalResidualNormalizedPartition dimensionCorrectedTemperature
  rw [Real.exp_sub,Real.exp_log (mixturePartition_pos hn θ _ J),div_eq_mul_inv,←Real.exp_neg]
  simp only [neg_div,neg_mul,mul_comm]

theorem actual_value_critical_residual_partition_law (n:ℕ) (hn:1 ≤ n)
    (μ:FiniteMixture) {Q:ℝ} (hQ:Q∈Ioo (0:ℝ) 1)
    (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ))
    (e:Vector n→ₗᵢ[ℝ] Vector (n+1)) (he:∀ y,inner ℝ (e y) u=0) (β e₀:ℝ) :
    let θ:=μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)
    (valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu e₀).map
      (actualCriticalResidualNormalizedPartition n μ hQ u e β e₀)=
      (disorderLaw n θ.maxDegree).map (physicalResidualNormalizedPartition n θ β):=by
  let U:=fun J:Disorder (n+1) μ.maxDegree=>actualCriticalBandContinuousField n n μ Q u e
    (fun x:CompactSphereCarrier.Carrier n=>x.val) continuous_subtype_val (euclideanDisorder J)
  have hU:Measurable U:=(actualCriticalBandContinuousField n n μ Q u e _ continuous_subtype_val).continuous.measurable.comp
    (euclideanDisorder_measurable _ _)
  exact critical_residual_partition_law_of_field_law _ n hn _ β U hU ((n+1:ℕ)*e₀)
    (actual_value_critical_band_continuous_law n n (by omega) μ hQ u hu e he _ continuous_subtype_val e₀)

theorem actual_mixed_critical_residual_partition_law (n:ℕ) (hn:1 ≤ n)
    (μ:FiniteMixture) {Q:ℝ} (hQ:Q∈Ioo (0:ℝ) 1) (hnp:μ.minDegree<μ.maxDegree)
    (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ))
    (e:Vector n→ₗᵢ[ℝ] Vector (n+1)) (he:∀ y,inner ℝ (e y) u=0) (β:ℝ)
    (b:EuclideanSpace ℝ (Fin 2)) :
    let θ:=μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)
    (mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b).map
      (actualCriticalResidualNormalizedPartition n μ hQ u e β (b 0))=
      (disorderLaw n θ.maxDegree).map (physicalResidualNormalizedPartition n θ β):=by
  let U:=fun J:Disorder (n+1) μ.maxDegree=>actualCriticalBandContinuousField n n μ Q u e
    (fun x:CompactSphereCarrier.Carrier n=>x.val) continuous_subtype_val (euclideanDisorder J)
  have hU:Measurable U:=(actualCriticalBandContinuousField n n μ Q u e _ continuous_subtype_val).continuous.measurable.comp
    (euclideanDisorder_measurable _ _)
  exact critical_residual_partition_law_of_field_law _ n hn _ β U hU ((n+1:ℕ)*b 0)
    (actual_mixed_critical_band_continuous_law n n (by omega) μ hQ hnp u hu e he _ continuous_subtype_val b)

/-- Source lem:mb-residual, its genuine proper-value critical realization:
the normalized partition stays away from zero, uniformly in all marks. -/
theorem actual_value_critical_residual_partition_lower_tail (μ:FiniteMixture)
    {β x Q:ℝ} (h:Certificate μ β x Q) :
    ∀ ε:ℝ,0<ε → ∃ t:ℝ,0<t ∧ ∀ᶠ n:ℕ in atTop,
      ∀ (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ))
        (e:Vector n→ₗᵢ[ℝ] Vector (n+1)) (_he:∀ y,inner ℝ (e y) u=0) (e₀:ℝ),
      (valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu e₀).real
        {J|actualCriticalResidualNormalizedPartition n μ h.overlap_range u e β e₀ J<t} ≤ ε:=by
  intro ε hε
  let θ:=μ.taylorResidual h.overlap_range.1 (sub_pos.mpr h.overlap_range.2)
  obtain ⟨τ,hTail⟩:=certified_physicalResidualNormalizedPartition_lower_tail h ε hε
  refine ⟨Real.exp (-τ),Real.exp_pos _,?_⟩
  filter_upwards [hTail,eventually_ge_atTop (1:ℕ)] with n hn hdim
  intro u hu e he e₀
  have H:=congrArg (fun ν:Measure ℝ=>ν.real (Iio (Real.exp (-τ))))
    (actual_value_critical_residual_partition_law n hdim μ h.overlap_range u hu e he β e₀)
  rw [map_measureReal_apply (actualCriticalResidualNormalizedPartition_measurable n hdim μ h.overlap_range u e β e₀)
      measurableSet_Iio,map_measureReal_apply (physicalResidualNormalizedPartition_measurable n θ β) measurableSet_Iio] at H
  exact H.trans_le hn

/-- Source lem:mb-residual for the actual mixed critical posterior. The
full continuous law proves uniformity in both value and radial marks. -/
theorem actual_mixed_critical_residual_partition_lower_tail (μ:FiniteMixture)
    {β x Q:ℝ} (h:Certificate μ β x Q) (hnp:μ.minDegree<μ.maxDegree) :
    ∀ ε:ℝ,0<ε → ∃ t:ℝ,0<t ∧ ∀ᶠ n:ℕ in atTop,
      ∀ (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ))
        (e:Vector n→ₗᵢ[ℝ] Vector (n+1)) (_he:∀ y,inner ℝ (e y) u=0)
        (b:EuclideanSpace ℝ (Fin 2)),
      (mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b).real
        {J|actualCriticalResidualNormalizedPartition n μ h.overlap_range u e β (b 0) J<t} ≤ ε:=by
  intro ε hε
  let θ:=μ.taylorResidual h.overlap_range.1 (sub_pos.mpr h.overlap_range.2)
  obtain ⟨τ,hTail⟩:=certified_physicalResidualNormalizedPartition_lower_tail h ε hε
  refine ⟨Real.exp (-τ),Real.exp_pos _,?_⟩
  filter_upwards [hTail,eventually_ge_atTop (1:ℕ)] with n hn hdim
  intro u hu e he b
  have H:=congrArg (fun ν:Measure ℝ=>ν.real (Iio (Real.exp (-τ))))
    (actual_mixed_critical_residual_partition_law n hdim μ h.overlap_range hnp u hu e he β b)
  rw [map_measureReal_apply (actualCriticalResidualNormalizedPartition_measurable n hdim μ h.overlap_range u e β (b 0))
      measurableSet_Iio,map_measureReal_apply (physicalResidualNormalizedPartition_measurable n θ β) measurableSet_Iio] at H
  exact H.trans_le hn

end
end SlowEquilibration.SphericalTAPCriticalBand
