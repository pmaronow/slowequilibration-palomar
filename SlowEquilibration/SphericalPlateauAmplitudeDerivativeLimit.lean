-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalWeightedTrialEnvelope
public import SlowEquilibration.SphericalPlateauAmplitudeDerivative
public import SlowEquilibration.SphericalPlateauAmplitudeExpected
public import SlowEquilibration.SphericalPlateauAmplitudeMeanContact
public import SlowEquilibration.ConvexTouchDerivative

@[expose] public section

/-! # Exact finite amplitude derivative from actual envelope contact

This analytic connector consumes only actual unperturbed pressure contact
and actual nearby envelope upper bounds. Physical finite derivatives,
convexity and the scalar envelope derivative are proved internally.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set Filter SphericalModel
open scoped Topology
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem amplitudePressureDerivative_tendsto_of_contact_upper (μ : FiniteMixture)
    {β δ q₁ q₂ ρ : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi<β)
    (hβs : β<Thresholds.staticThreshold μ.xi) (hc : IsAdmissibleCollar μ β q₁ q₂)
    (hδ : 0≤δ) (p₀ : Degree μ.maxDegree) (k : Fin 2)
    (hqρ : Thresholds.qStar μ.xi β≤ρ) (hρ : ρ<1)
    (x : (n : ℕ) → Vector (n+1))
    (hTouch : Tendsto (fun n => amplitudeExpectedPressure μ β (plantedCoreCost μ β) δ q₁ q₂
      (x n) (latitudeFrameAt (x n)) p₀ (fun _ => 1)) atTop
      (𝓝 (β^2*μ.xi 1/2-plantedCoreCost μ β)))
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
  obtain ⟨hZero,hDeriv⟩ := weightedAmplitudeTrialEnvelope_contact_derivative μ hβ hβs hc hδ p₀ k hqρ hρ
  apply ConvexTouchDerivative.tendsto_derivatives_of_touching_upper_trial
    (fun n τ => amplitudeExpectedPressure μ β (plantedCoreCost μ β) δ q₁ q₂
      (x n) (latitudeFrameAt (x n)) p₀ (amplitudeAt k τ)) _
    (weightedAmplitudeTrialEnvelope μ β δ q₁ q₂ p₀ k ρ
      ((μ.qStar_solves_plateau hβ).1.1.le.trans hqρ) hρ) 0 (1/2) _ (by norm_num)
  · intro n
    exact (amplitudeExpectedPressure_line_convex μ β (plantedCoreCost μ β) δ q₁ q₂
      (x n) (latitudeFrameAt (x n)) p₀ k).subset (subset_univ _) (convex_Icc _ _)
  · intro n
    exact amplitudeExpectedPressure_hasDerivAt μ β (plantedCoreCost μ β) δ q₁ q₂
      (x n) (latitudeFrameAt (x n)) p₀ k 0
  · exact hDeriv
  · simpa only [amplitudeAt_zero,hZero] using hTouch
  · simpa only [zero_sub,zero_add,neg_div] using hUpper

/-- In the proved globally convex class the contact input is already a
true model theorem; only the sampled/coarea nearby upper is consumed. -/
theorem convex_amplitudePressureDerivative_tendsto_of_upper (μ : FiniteMixture)
    (hconv : ConvexOn ℝ (Icc (-1:ℝ) 1) μ.xi)
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
        (1-(Thresholds.qStar μ.xi β/(1+Thresholds.qStar μ.xi β))^(k.val+1)))) :=
  amplitudePressureDerivative_tendsto_of_contact_upper μ hβ hβs hc hδ p₀ k hqρ hρ x
    (convex_amplitudeExpectedPressure_one_tendsto μ hconv hβ hβs.le hδ hc p₀ x hx) hUpper

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
