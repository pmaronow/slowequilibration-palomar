-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGeneralWeightedMeanLower

@[expose] public section

/-! # Genuine all-finite weighted denominator lower tail in the actual bank -/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalBarycenter SphericalSourceWeightedPartition
open scoped Topology ENNReal
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

theorem amplitudePartition_pos (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (D : BankDisorder n μ) :
    0<amplitudePartition μ β J δ q₁ q₂ x e p₀ s D := by
  unfold amplitudePartition
  apply integral_exp_pos
  apply integrable_sphere_of_continuous (by omega : 1≤n+1)
  have hR : Continuous (fun u : Vector (n+1) => overlap x u) := by unfold overlap;fun_prop
  exact Real.continuous_exp.comp (((amplitudePlantedField_contDiff μ β x e p₀ s D).continuous.const_mul β).sub
    (continuous_const.mul ((sourceProfile_contDiff J δ q₁ q₂).continuous.comp hR)))

theorem general_amplitudeWeightedPressure_closed_lower_tail (μ : FiniteMixture)
    {β δ q₁ q₂ ε : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi<β)
    (hc : IsAdmissibleCollar μ β q₁ q₂) (hε : 0<ε) (p₀ : Degree μ.maxDegree) :
    ∃ γ : ℝ,0<γ ∧ ∀ᶠ n : ℕ in atTop,∀ x : Vector (n+1),‖x‖^2=((n+1:ℕ):ℝ) →
      bankLaw n μ {D | Real.log (amplitudePartition μ β (plantedCoreCost μ β) δ q₁ q₂
        x (latitudeFrameAt x) p₀ (fun _ => 1) D)/((n+1:ℕ):ℝ)≤
        β^2*μ.xi 1/2-plantedCoreCost μ β-ε}≤6*ENNReal.ofReal (Real.exp (-γ*((n+1:ℕ):ℝ))) := by
  obtain ⟨γ,hγ,hTail⟩ := general_sourceWeightedPlantedPressure_closed_lower_tail μ (δ := δ) hβ hc hε
  refine ⟨γ,hγ,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hTail] with n hn
  intro x hx
  let B : Set ℝ := {y | y/((n+1:ℕ):ℝ)≤β^2*μ.xi 1/2-plantedCoreCost μ β-ε}
  have hB : MeasurableSet B := measurableSet_le (measurable_id.div_const _) measurable_const
  have hLaw := amplitudePartition_log_law_one μ β (plantedCoreCost μ β) δ q₁ q₂ x
    (by simpa only [Nat.cast_add,Nat.cast_one] using hx) p₀
  have he := congrArg (fun ν : Measure ℝ => ν B) hLaw
  rw [Measure.map_apply (amplitudePartition_log_measurable_one μ β (plantedCoreCost μ β) δ q₁ q₂ x p₀) hB,
    Measure.map_apply (originalWeightedPartition_log_measurable μ β (plantedCoreCost μ β) δ q₁ q₂ x) hB] at he
  change bankLaw n μ {D | Real.log (amplitudePartition μ β (plantedCoreCost μ β) δ q₁ q₂ x
    (latitudeFrameAt x) p₀ (fun _ => 1) D)/((n+1:ℕ):ℝ)≤β^2*μ.xi 1/2-plantedCoreCost μ β-ε}=
    disorderLaw (n+1) μ.maxDegree {D | sourceWeightedPlantedPressure μ β δ q₁ q₂ x D≤
      β^2*μ.xi 1/2-plantedCoreCost μ β-ε} at he
  rw [he]
  exact hn x hx

/-- The literal actual weighted partition cannot fall below its source
core exponent except with exponentially small bank probability. -/
theorem general_amplitudePartition_closed_lower_tail (μ : FiniteMixture)
    {β δ q₁ q₂ ε : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi<β)
    (hc : IsAdmissibleCollar μ β q₁ q₂) (hε : 0<ε) (p₀ : Degree μ.maxDegree) :
    ∃ γ : ℝ,0<γ ∧ ∀ᶠ n : ℕ in atTop,∀ x : Vector (n+1),‖x‖^2=((n+1:ℕ):ℝ) →
      bankLaw n μ {D | amplitudePartition μ β (plantedCoreCost μ β) δ q₁ q₂
        x (latitudeFrameAt x) p₀ (fun _ => 1) D≤
        Real.exp (((n+1:ℕ):ℝ)*(β^2*μ.xi 1/2-plantedCoreCost μ β-ε))}≤
        6*ENNReal.ofReal (Real.exp (-γ*((n+1:ℕ):ℝ))) := by
  obtain ⟨γ,hγ,hTail⟩ := general_amplitudeWeightedPressure_closed_lower_tail μ (δ := δ) hβ hc hε p₀
  refine ⟨γ,hγ,?_⟩
  filter_upwards [hTail] with n hn
  intro x hx
  apply (measure_mono ?_).trans (hn x hx)
  intro D hD
  have hp := amplitudePartition_pos μ β (plantedCoreCost μ β) δ q₁ q₂ x (latitudeFrameAt x) p₀ (fun _ => 1) D
  have hh := Real.log_le_log hp hD
  rw [Real.log_exp] at hh
  exact (div_le_iff₀ (by positivity : 0<((n+1:ℕ):ℝ))).mpr (by nlinarith)

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
