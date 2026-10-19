-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPositivePartitionUpper
public import SlowEquilibration.SphericalCoreLikelihoodTransfer
public import SlowEquilibration.SphericalGoodCapCoreCollar
public import SlowEquilibration.PlantedCollarGeometry

/-! Actual cap, core and collar partition tests have exponentially small
joint Gibbs-reference failure. The core comes from the conditioned critical
point construction, while the upper tests come from sampled coarea bounds. -/

@[expose] public section
namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter SphericalTaylorRemainder
open scoped Topology
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem convex_gibbsReference_positive_partition_upper_tail (μ : FiniteMixture)
    (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi) {β M ε : ℝ}
    (hβ : 0 < β) (hβs : β ≤ Thresholds.staticThreshold μ.xi) (hε : 0 < ε)
    {A : Set ℝ} (hA : MeasurableSet A)
    (hpos : ∀ q ∈ A, q ∈ Ioo (-1 : ℝ) 1 → 0 ≤ q)
    (htrial : ∀ q ∈ A, q ∈ Ioo (-1 : ℝ) 1 → plantedProfileTrial μ β q ≤ M) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      (gibbsReferenceLaw (mixtureCoefficients μ) β).real
        (positivePartitionUpperBadEvent N μ β M ε A) ≤ 3 * Real.exp (-c * (N : ℝ)) := by
  obtain ⟨γ,hγ,hP⟩ := convex_planted_positive_partition_upper_tail μ hconv hβ hε hA hpos htrial
  have hPr : ∀ᶠ N : ℕ in atTop,
      (plantedLaw (mixtureCoefficients μ) β).real (positivePartitionUpperBadEvent N μ β M ε A) ≤
        Real.exp (-γ * (N : ℝ)) := by
    filter_upwards [hP] with N hN
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hN).trans_eq
      (ENNReal.toReal_ofReal (Real.exp_pos _).le)
  refine ⟨plantedTransferRate μ β γ,plantedTransferRate_pos μ hβ hγ,?_⟩
  exact exponential_planted_transfer_eventually_of_pressure_limit μ hβ hγ
    (convex_quenchedPressure_tendsto_annealed_le_static μ hconv hβ.le hβs)
    (fun N => positivePartitionUpperBadEvent N μ β M ε A)
    (fun N => positivePartitionUpperBadEvent_measurable N μ β M ε hA) hPr

theorem capCoreCollarBadEvent_eq_union (N : ℕ) (μ : FiniteMixture)
    (β δ q₁ q₂ w : ℝ) :
    capCoreCollarBadEvent (N := N) (mixtureCoefficients μ) β
      (β^2*μ.xi 1/2) (plantedCoreCost μ β) (plantedCollarGap μ β q₂) δ
      q₁ q₂ (Thresholds.qStar μ.xi β) w =
    positivePartitionUpperBadEvent N μ β (β^2*μ.xi 1/2-plantedCoreCost μ β) δ (Ici q₁) ∪
      (coreLowerBadEvent N μ β w δ ∪ positivePartitionUpperBadEvent N μ β
        (β^2*μ.xi 1/2-plantedCoreCost μ β-plantedCollarGap μ β q₂) δ (Icc q₁ q₂)) := by
  ext z
  simp only [capCoreCollarBadEvent,badReferenceEvent,positivePartitionUpperBadEvent,
    coreLowerBadEvent,mem_union,mem_ofPred_eq]
  rw [plantedProfileTrial_qStar_eq,coreBand_eq_overlapRegion]
  rfl

/-- The complete literal cap/core/collar partition-test event under the
actual Gibbs-reference law. Every stochastic estimate is proved internally. -/
theorem convex_gibbsReference_capCoreCollar_bad_tail (μ : FiniteMixture)
    (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi) {β δ q₁ q₂ w : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β)
    (hβs : β ≤ Thresholds.staticThreshold μ.xi)
    (hc : IsAdmissibleCollar μ β q₁ q₂) (hδ : 0 < δ) (hw : 0 < w) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      (gibbsReferenceLaw (mixtureCoefficients μ) β).real
        (capCoreCollarBadEvent (N := N) (mixtureCoefficients μ) β
          (β^2*μ.xi 1/2) (plantedCoreCost μ β) (plantedCollarGap μ β q₂) δ
          q₁ q₂ (Thresholds.qStar μ.xi β) w) ≤ 9 * Real.exp (-c * (N : ℝ)) := by
  have hβpos : 0 < β := μ.dynamicalThreshold_pos.trans hβ
  obtain ⟨hcap,hcollar⟩ := plantedProfileTrial_cap_collar_bounds μ hβ hc
  obtain ⟨c₁,hc₁,h₁⟩ := convex_gibbsReference_positive_partition_upper_tail μ hconv hβpos hβs hδ
    measurableSet_Ici (fun q hq _ => hc.1.le.trans hq) (fun q hq hq' => hcap q ⟨hq,hq'.2⟩)
  obtain ⟨c₂,hc₂,h₂⟩ := convex_gibbsReference_core_partition_lower_tail μ hconv hβ hβs hw hδ
  obtain ⟨c₃,hc₃,h₃⟩ := convex_gibbsReference_positive_partition_upper_tail μ hconv hβpos hβs hδ
    measurableSet_Icc (fun q hq _ => hc.1.le.trans hq.1) (fun q hq _ => hcollar q hq)
  let c := min c₁ (min c₂ c₃)
  have hcpos : 0 < c := lt_min hc₁ (lt_min hc₂ hc₃)
  refine ⟨c,hcpos,?_⟩
  filter_upwards [h₁,h₂,h₃] with N hN₁ hN₂ hN₃
  have he (a : ℝ) (ha : c ≤ a) : Real.exp (-a * (N : ℝ)) ≤ Real.exp (-c * (N : ℝ)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg ha) (Nat.cast_nonneg N)
  have he₁ := he c₁ (min_le_left _ _)
  have he₂ := he c₂ ((min_le_right _ _).trans (min_le_left _ _))
  have he₃ := he c₃ ((min_le_right _ _).trans (min_le_right _ _))
  rw [capCoreCollarBadEvent_eq_union]
  apply (measureReal_union_le _ _).trans
  apply (add_le_add hN₁ ((measureReal_union_le _ _).trans (add_le_add hN₂ hN₃))).trans
  linarith

theorem even_gibbsReference_capCoreCollar_bad_tail (μ : FiniteMixture)
    (heven : ∀ p ∈ μ.coeff.support, Even p) {β δ q₁ q₂ w : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β)
    (hβs : β ≤ Thresholds.staticThreshold μ.xi)
    (hc : IsAdmissibleCollar μ β q₁ q₂) (hδ : 0 < δ) (hw : 0 < w) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      (gibbsReferenceLaw (mixtureCoefficients μ) β).real
        (capCoreCollarBadEvent (N := N) (mixtureCoefficients μ) β
          (β^2*μ.xi 1/2) (plantedCoreCost μ β) (plantedCollarGap μ β q₂) δ
          q₁ q₂ (Thresholds.qStar μ.xi β) w) ≤ 9 * Real.exp (-c * (N : ℝ)) :=
  convex_gibbsReference_capCoreCollar_bad_tail μ (μ.convexOn_xi_Icc_of_even heven)
    hβ hβs hc hδ hw

end
end SlowEquilibration.SphericalModel
