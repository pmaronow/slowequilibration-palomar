-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeMeanUpperTransfer
public import SlowEquilibration.SphericalPlateauAmplitudeWeightedSampleUpper

@[expose] public section

/-! # Genuine nearby weighted amplitude mean envelope upper

The physical sampled bound is proved by the actual latitude/coarea and polar
estimates. The actual weighted Gaussian concentration then bounds the literal
expected pressure. The radius is chosen once before all source tolerances.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Genuine nearby source-amplitude expected pressure upper, without an
externally supplied sampled-pressure, mean-pressure or positivity premise. -/
theorem exists_amplitudeExpectedPressure_uniform_envelope_upper
    (μ : FiniteMixture) {β δ q₁ q₂ : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi<β)
    (hβs : β<Thresholds.staticThreshold μ.xi)
    (hc : IsAdmissibleCollar μ β q₁ q₂) (hδ : 0≤δ) (p₀ : Degree μ.maxDegree) :
    ∃ ρ : ℝ,∃ hqρ : Thresholds.qStar μ.xi β≤ρ,∃ hρ : ρ<1,
      0<ρ ∧ ∀ ε : ℝ,0<ε → ∀ᶠ n : ℕ in atTop,
        ∀ (k : Fin 2) (τ : ℝ),τ∈Icc (-1/2 : ℝ) (1/2) →
        ∀ (x : Vector (n+1)),‖x‖^2=((n+1 : ℕ) : ℝ) →
          amplitudeExpectedPressure μ β (plantedCoreCost μ β) δ q₁ q₂
            x (latitudeFrameAt x) p₀ (amplitudeAt k τ)≤
          weightedAmplitudeTrialEnvelope μ β δ q₁ q₂ p₀ k ρ
            ((μ.qStar_solves_plateau hβ).1.1.le.trans hqρ) hρ τ+ε := by
  obtain ⟨ρ,hqρ,hρ,hρ0,hsample⟩ := exists_amplitudeWeightedSampledPressure_upper μ hβ hβs hc hδ p₀
  refine ⟨ρ,hqρ,hρ,hρ0,?_⟩
  intro ε hε
  exact amplitudeExpectedPressure_eventually_upper_of_sampled_upper μ
    (μ.dynamicalThreshold_pos.trans hβ) (plantedCoreCost μ β) δ q₁ q₂ p₀
    (fun k τ => weightedAmplitudeTrialEnvelope μ β δ q₁ q₂ p₀ k ρ
      ((μ.qStar_solves_plateau hβ).1.1.le.trans hqρ) hρ τ) hsample hε


/-- The same genuine upper in the latitude-axis sequence format used by the
physical source derivative theorem. -/
theorem exists_amplitudeExpectedPressure_sequence_envelope_upper
    (μ : FiniteMixture) {β δ q₁ q₂ : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi<β)
    (hβs : β<Thresholds.staticThreshold μ.xi)
    (hc : IsAdmissibleCollar μ β q₁ q₂) (hδ : 0≤δ) (p₀ : Degree μ.maxDegree)
    (x : (n : ℕ) → Vector (n+1)) (hx : ∀ n,‖x n‖^2=((n+1 : ℕ) : ℝ)) :
    ∃ ρ : ℝ,∃ hqρ : Thresholds.qStar μ.xi β≤ρ,∃ hρ : ρ<1,
      ∀ k : Fin 2,∀ τ∈Ioo (-1/2 : ℝ) (1/2),∀ ε : ℝ,0<ε → ∀ᶠ n : ℕ in atTop,
        amplitudeExpectedPressure μ β (plantedCoreCost μ β) δ q₁ q₂
          (x n) (latitudeFrameAt (x n)) p₀ (amplitudeAt k τ)≤
        weightedAmplitudeTrialEnvelope μ β δ q₁ q₂ p₀ k ρ
          ((μ.qStar_solves_plateau hβ).1.1.le.trans hqρ) hρ τ+ε := by
  obtain ⟨ρ,hqρ,hρ,_hρ0,hupper⟩ := exists_amplitudeExpectedPressure_uniform_envelope_upper μ hβ hβs hc hδ p₀
  refine ⟨ρ,hqρ,hρ,?_⟩
  intro k τ hτ ε hε
  filter_upwards [hupper ε hε] with n hn
  exact hn k τ ⟨hτ.1.le,hτ.2.le⟩ (x n) (hx n)

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
