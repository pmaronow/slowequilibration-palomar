-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGeneralTaylorCore
public import SlowEquilibration.SphericalGeneralRSPressure
public import SlowEquilibration.SphericalExponentialTransfer
public import SlowEquilibration.SphericalEvenCovariance
public import SlowEquilibration.SphericalGoodReference

/-! The actual core lower event under the Gibbs-reference law, followed by
its quenched good-reference estimate. Both estimates use the proved planted
core construction and the proved convex-covariance RS pressure limit. -/

@[expose] public section
namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter SphericalTaylorRemainder
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem general_gibbsReference_core_partition_lower_tail (μ : FiniteMixture)
    {β δ ε : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β)
    (hβs : β ≤ Thresholds.staticThreshold μ.xi) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      (gibbsReferenceLaw (mixtureCoefficients μ) β).real
        (coreLowerBadEvent N μ β δ ε) ≤ 3 * Real.exp (-c * (N : ℝ)) := by
  obtain ⟨γ, hγ, hP⟩ := GeneralFinite.qStar_planted_core_partition_lower_tail_allDimensions μ hβ hδ hε
  have hβpos : 0 < β := μ.dynamicalThreshold_pos.trans hβ
  have hPr : ∀ᶠ N : ℕ in atTop,
      (plantedLaw (mixtureCoefficients μ) β).real (coreLowerBadEvent N μ β δ ε) ≤
        Real.exp (-γ * (N : ℝ)) := by
    filter_upwards [hP] with N hN
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hN).trans_eq
      (ENNReal.toReal_ofReal (Real.exp_pos _).le)
  refine ⟨plantedTransferRate μ β γ, plantedTransferRate_pos μ hβpos hγ, ?_⟩
  exact exponential_planted_transfer_eventually_of_pressure_limit μ hβpos hγ
    (general_quenchedPressure_tendsto_annealed_le_static μ hβpos.le hβs)
    (fun N => coreLowerBadEvent N μ β δ ε)
    (fun N => coreLowerBadEvent_measurable N μ β δ ε) hPr

theorem general_goodReference_core_partition_lower_tail (μ : FiniteMixture)
    {β δ ε : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β)
    (hβs : β ≤ Thresholds.staticThreshold μ.xi) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      (disorderLaw N μ.maxDegree).real
        {J | Real.exp (-c * (N : ℝ)) <
          (gibbsLaw N β (fieldOfMixture μ J)).real
            (goodReferenceSet (coreLowerBadEvent N μ β δ ε) J)ᶜ} ≤
        3 * Real.exp (-c * (N : ℝ)) := by
  obtain ⟨c, hc, hQ⟩ := general_gibbsReference_core_partition_lower_tail μ hβ hβs hδ hε
  refine ⟨c / 2, half_pos hc, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), hQ] with N hN hQN
  apply (goodReferenceSet_failure_le hN (mixtureCoefficients μ) β
    (coreLowerBadEvent_measurable N μ β δ ε) (Real.exp_pos (-(c / 2) * (N : ℝ)))).trans
  calc
    _ ≤ (3 * Real.exp (-c * (N : ℝ))) / Real.exp (-(c / 2) * (N : ℝ)) :=
      div_le_div_of_nonneg_right hQN (Real.exp_pos _).le
    _ = _ := by rw [mul_div_assoc, ← Real.exp_sub]; congr 2; ring

end
end SlowEquilibration.SphericalModel
