-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGeneralWeightedMeanLower
public import SlowEquilibration.SphericalPlateauAmplitudeDerivativeLimit

@[expose] public section

/-! # General finite pressure contact and derivative from the actual upper

The genuine canonical core mean lower closes the contact obligation once
the sampled/coarea envelope upper is supplied. All scalar uniqueness,
contact and finite convex derivative calculations are proved internally.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set Filter SphericalModel
open scoped Topology
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem general_amplitudeExpectedPressure_one_tendsto_of_upper (μ : FiniteMixture)
    {β δ q₁ q₂ ρ : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi<β)
    (hβs : β<Thresholds.staticThreshold μ.xi) (hc : IsAdmissibleCollar μ β q₁ q₂)
    (hδ : 0≤δ) (p₀ : Degree μ.maxDegree) (k : Fin 2)
    (hqρ : Thresholds.qStar μ.xi β≤ρ) (hρ : ρ<1)
    (x : (n : ℕ) → Vector (n+1)) (hx : ∀ n,‖x n‖^2=(n+1:ℝ))
    (hUpper : ∀ ε : ℝ,0<ε → ∀ᶠ n : ℕ in atTop,
      amplitudeExpectedPressure μ β (plantedCoreCost μ β) δ q₁ q₂
        (x n) (latitudeFrameAt (x n)) p₀ (fun _ => 1)≤
      weightedAmplitudeTrialEnvelope μ β δ q₁ q₂ p₀ k ρ
        ((μ.qStar_solves_plateau hβ).1.1.le.trans hqρ) hρ 0+ε) :
    Tendsto (fun n => amplitudeExpectedPressure μ β (plantedCoreCost μ β) δ q₁ q₂
      (x n) (latitudeFrameAt (x n)) p₀ (fun _ => 1)) atTop
      (𝓝 (β^2*μ.xi 1/2-plantedCoreCost μ β)) := by
  have hZero := (weightedAmplitudeTrialEnvelope_contact_derivative μ hβ hβs hc hδ p₀ k hqρ hρ).1
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [general_amplitudeExpectedPressure_one_eventually_ge μ (δ := δ) hβ hc (half_pos hε) p₀,
    hUpper (ε/2) (half_pos hε)] with n hLower hUpperN
  have hLow := hLower (x n) (hx n)
  rw [hZero] at hUpperN
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> linarith

/-- Exact source amplitude derivative convergence for every finite mixture
once its actual nearby coarea envelope upper is proved. -/
theorem general_amplitudePressureDerivative_tendsto_of_upper (μ : FiniteMixture)
    {β δ q₁ q₂ ρ : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi<β)
    (hβs : β<Thresholds.staticThreshold μ.xi) (hc : IsAdmissibleCollar μ β q₁ q₂)
    (hδ : 0≤δ) (p₀ : Degree μ.maxDegree) (k : Fin 2)
    (hqρ : Thresholds.qStar μ.xi β≤ρ) (hρ : ρ<1)
    (x : (n : ℕ) → Vector (n+1)) (hx : ∀ n,‖x n‖^2=(n+1:ℝ))
    (hUpper : ∀ τ∈Ioo (-1/2:ℝ) (1/2),∀ ε : ℝ,0<ε → ∀ᶠ n : ℕ in atTop,
      amplitudeExpectedPressure μ β (plantedCoreCost μ β) δ q₁ q₂
        (x n) (latitudeFrameAt (x n)) p₀ (amplitudeAt k τ)≤
      weightedAmplitudeTrialEnvelope μ β δ q₁ q₂ p₀ k ρ
        ((μ.qStar_solves_plateau hβ).1.1.le.trans hqρ) hρ τ+ε) :
    Tendsto (fun n => amplitudePressureDerivative μ β (plantedCoreCost μ β) δ q₁ q₂
      (x n) (latitudeFrameAt (x n)) p₀ k 0) atTop
      (𝓝 (β^2*SphericalPlateauAmplitudeScalars.amplitudeSq (mixtureCoefficients μ p₀)
        p₀.val.val (k.val+1) (Thresholds.qStar μ.xi β)*
        (1-(Thresholds.qStar μ.xi β/(1+Thresholds.qStar μ.xi β))^(k.val+1)))) := by
  apply amplitudePressureDerivative_tendsto_of_contact_upper μ hβ hβs hc hδ p₀ k hqρ hρ x _ hUpper
  apply general_amplitudeExpectedPressure_one_tendsto_of_upper μ hβ hβs hc hδ p₀ k hqρ hρ x hx
  intro ε hε
  simpa only [amplitudeAt_zero] using hUpper 0 (by constructor <;> norm_num) ε hε

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
