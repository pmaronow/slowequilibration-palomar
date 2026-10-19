-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudePressureLaw
public import SlowEquilibration.SphericalWeightedPlantedMean

@[expose] public section

/-! # Genuine amplitude-one expected-pressure contact

The actual original-tensor planted-pressure estimate and the whole bank
field law prove the center contact used by the convex derivative squeeze.No limiting pressure hypothesis appears in the exported contact theorem.-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalBarycenter SphericalSourceWeightedPartition
open SphericalTaylorRemainder WholeFieldRegression
open scoped Topology
set_option maxHeartbeats 1450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

theorem amplitudePartition_log_measurable_one (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (p₀ : Degree μ.maxDegree) :
    Measurable (fun D : BankDisorder n μ => Real.log
      (amplitudePartition μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ (fun _ => 1) D)) := by
  have he : (fun D : BankDisorder n μ => Real.log
      (amplitudePartition μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ (fun _ => 1) D))=
      weightedLogPartitionFunctional μ β J δ q₁ q₂ x ∘ fun D =>
        bankContinuousField μ x (latitudeFrameAt x) p₀ (fun _ => 1)
          (Subtype.val : CompactSphereCarrier.Carrier (n+1) → Vector (n+1)) continuous_subtype_val (euclideanBank D) := by
    funext D
    exact (weightedLogPartitionFunctional_bank μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ (fun _ => 1) D).symm
  rw [he]
  exact (weightedLogPartitionFunctional_measurable μ β J δ q₁ q₂ x).comp
    ((bankContinuousField μ x (latitudeFrameAt x) p₀ (fun _ => 1)
      (Subtype.val : CompactSphereCarrier.Carrier (n+1) → Vector (n+1)) continuous_subtype_val).continuous.measurable.comp (euclideanBank_measurable n μ))

theorem originalWeightedPartition_log_measurable (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) : Measurable (fun D : Disorder (n+1) μ.maxDegree => Real.log
      (sourceWeightedPartition β (fieldOfMixture μ (D+plantedShift (mixtureCoefficients μ) β x)) J δ q₁ q₂ x)) := by
  have he : (fun D : Disorder (n+1) μ.maxDegree => Real.log
      (sourceWeightedPartition β (fieldOfMixture μ (D+plantedShift (mixtureCoefficients μ) β x)) J δ q₁ q₂ x))=
      weightedLogPartitionFunctional μ β J δ q₁ q₂ x ∘ fun D =>
        modelContinuousField (mixtureCoefficients μ)
          (Subtype.val : CompactSphereCarrier.Carrier (n+1) → Vector (n+1)) continuous_subtype_val (euclideanDisorder D) := by
    funext D
    exact (weightedLogPartitionFunctional_original μ β J δ q₁ q₂ x D).symm
  rw [he]
  exact (weightedLogPartitionFunctional_measurable μ β J δ q₁ q₂ x).comp
    ((modelContinuousField (mixtureCoefficients μ)
      (Subtype.val : CompactSphereCarrier.Carrier (n+1) → Vector (n+1)) continuous_subtype_val).continuous.measurable.comp (euclideanDisorder_measurable _ _))

/-- Exact normalized expectation transport from the bank to the original
Gaussian disorder and its true covariance translation. -/
theorem amplitudeExpectedPressure_one_eq_originalMean (μ : FiniteMixture) (β δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (hx : ‖x‖^2=(n+1:ℝ)) (p₀ : Degree μ.maxDegree) :
    amplitudeExpectedPressure μ β (plantedCoreCost μ β) δ q₁ q₂ x (latitudeFrameAt x) p₀ (fun _ => 1)=
      ∫ D,sourceWeightedPlantedPressure μ β δ q₁ q₂ x D ∂disorderLaw (n+1) μ.maxDegree := by
  have hBank := integral_map (μ := bankLaw n μ) (amplitudePartition_log_measurable_one μ β (plantedCoreCost μ β) δ q₁ q₂ x p₀).aemeasurable
    (stronglyMeasurable_id.aestronglyMeasurable)
  have hOriginal := integral_map (μ := disorderLaw (n+1) μ.maxDegree) (originalWeightedPartition_log_measurable μ β (plantedCoreCost μ β) δ q₁ q₂ x).aemeasurable
    (stronglyMeasurable_id.aestronglyMeasurable)
  simp only [id_eq] at hBank hOriginal
  rw [amplitudePartition_log_law_one μ β (plantedCoreCost μ β) δ q₁ q₂ x hx p₀] at hBank
  rw [sourceWeightedPlantedMean_eq_logIntegral]
  unfold amplitudeExpectedPressure
  have he := hBank.symm.trans hOriginal
  simpa only [Nat.cast_add,Nat.cast_one] using congrArg (fun z : ℝ => z/(n+1:ℝ)) he

/-- True center contact for the finite source amplitude pressure, with all
probability and pressure estimates proved internally in the convex class. -/
theorem convex_amplitudeExpectedPressure_one_tendsto (μ : FiniteMixture)
    (hconv : ConvexOn ℝ (Icc (-1:ℝ) 1) μ.xi) {β δ q₁ q₂ : ℝ}
    (hβd : Thresholds.dynamicalThreshold μ.xi < β)
    (hβs : β ≤ Thresholds.staticThreshold μ.xi) (hδ : 0 ≤ δ)
    (hc : IsAdmissibleCollar μ β q₁ q₂) (p₀ : Degree μ.maxDegree)
    (x : (n : ℕ) → Vector (n+1)) (hx : ∀ n,‖x n‖^2=(n+1:ℝ)) :
    Tendsto (fun n => amplitudeExpectedPressure μ β (plantedCoreCost μ β) δ q₁ q₂
      (x n) (latitudeFrameAt (x n)) p₀ (fun _ => 1)) atTop
      (𝓝 (β^2*μ.xi 1/2-plantedCoreCost μ β)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hClose := (tendsto_add_atTop_nat 1).eventually
    (convex_sourceWeightedPlantedMean_eventually_close μ hconv hβd hβs hδ hc hε)
  filter_upwards [hClose] with n hn
  rw [amplitudeExpectedPressure_one_eq_originalMean μ β δ q₁ q₂ (x n) (hx n) p₀]
  simpa only [Real.dist_eq] using hn (x n) (by simpa only [Nat.cast_add,Nat.cast_one] using hx n)

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
