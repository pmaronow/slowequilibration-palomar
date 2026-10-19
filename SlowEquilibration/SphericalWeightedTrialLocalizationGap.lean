-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalWeightedTrialEnvelope

@[expose] public section

/-! # Actual strict weighted latitude gap away from the source maximizer

Compactness upgrades the proved unique global source trial maximizer to
a positive gap outside every fixed neighborhood. No curvature premise
enters the localization estimate.
-/
namespace SlowEquilibration.SphericalModel
noncomputable section
open Set Filter
open scoped Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem weightedAmplitudeTrialProfile_away_gap (μ : FiniteMixture)
    {β δ q₁ q₂ ρ ε : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi<β)
    (hβs : β<Thresholds.staticThreshold μ.xi) (hc : IsAdmissibleCollar μ β q₁ q₂)
    (hδ : 0≤δ) (hρ : ρ<1) (hε : 0<ε) :
    ∃ η : ℝ, 0<η ∧ ∀ r : ℝ, |r|≤ρ → ε≤|r-Thresholds.qStar μ.xi β| →
      weightedAmplitudeTrialProfile μ β δ q₁ q₂ r≤β^2*μ.xi 1/2-plantedCoreCost μ β-η := by
  let φ : WeightedTrialLatitude ρ → ℝ := fun r => weightedAmplitudeTrialProfile μ β δ q₁ q₂ r
  let A : Set (WeightedTrialLatitude ρ) := {r | ε≤|(r:ℝ)-Thresholds.qStar μ.xi β|}
  have hφ : Continuous φ := weightedAmplitudeTrialProfile_compact_continuous μ β δ q₁ q₂ hρ
  have hA : IsCompact A := (isClosed_le continuous_const
    ((continuous_subtype_val.sub continuous_const).abs)).isCompact
  by_cases hne : A.Nonempty
  · obtain ⟨r₀,hr₀,hm⟩ := hA.exists_isMaxOn hne hφ.continuousOn
    have hr01 : (r₀:ℝ)∈Ioo (-1:ℝ) 1 :=
      abs_lt.mp ((weightedTrialLatitude_abs_le r₀).trans_lt hρ)
    have hstrict : φ r₀<β^2*μ.xi 1/2-plantedCoreCost μ β := by
      by_contra hh
      have heq := weightedAmplitudeTrialProfile_unique_maximum μ hβ hβs hc hδ hr01 (le_of_not_gt hh)
      change ε≤|(r₀:ℝ)-Thresholds.qStar μ.xi β| at hr₀
      rw [heq,sub_self,abs_zero] at hr₀
      linarith
    refine ⟨(β^2*μ.xi 1/2-plantedCoreCost μ β-φ r₀)/2,by linarith,?_⟩
    intro r hr he
    let r' : WeightedTrialLatitude ρ := ⟨r,abs_le.mp hr⟩
    have hle : φ r'≤φ r₀ := hm (show r'∈A from he)
    change weightedAmplitudeTrialProfile μ β δ q₁ q₂ r≤_ at hle
    linarith
  · refine ⟨1,by norm_num,?_⟩
    intro r hr he
    exact False.elim (hne ⟨⟨r,abs_le.mp hr⟩,he⟩)

end
end SlowEquilibration.SphericalModel
