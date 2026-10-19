-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeProbeMomentExtraction
public import SlowEquilibration.SphericalGeneralAmplitudeContactDerivative

@[expose] public section

/-! # Actual physical moment limit from genuine envelope evidence

The caller supplies actual pressure contact, the nearby actual envelope
upper bound, and actual bank latitude localization. Finite derivatives,
convexity, replica integration by parts and both positive probe moment
extractions are internal proved providers.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter SphericalModel
open scoped Topology
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem amplitudeSourceDerivativeTarget_eq_diracShift (μ : FiniteMixture) (β : ℝ)
    (p₀ : Degree μ.maxDegree) (k : Fin 2) {q : ℝ} (hq : 0≤q) :
    β^2*SphericalPlateauAmplitudeScalars.amplitudeSq (mixtureCoefficients μ p₀)
      p₀.val.val (k.val+1) q*(1-(q/(1+q))^(k.val+1))=
      2*amplitudeDiracShiftCoefficient μ β p₀ k q := by
  unfold amplitudeDiracShiftCoefficient amplitudeDiracAtom
  rw [abs_of_nonneg hq]
  unfold amplitudeSelectedCoefficient SphericalPlateauAmplitudeScalars.amplitudeSq
  ring

theorem amplitudeNormError_tendsto_of_pairError (μ : FiniteMixture)
    (β J δ q₁ q₂ : ℝ) {q : ℝ} (hq : q∈Icc (0:ℝ) 1) (p₀ : Degree μ.maxDegree)
    (x : (n : ℕ) → Vector (n+1))
    (hPair : Tendsto (fun n => ∫ D,amplitudePairError μ β J δ q₁ q₂ q
      (x n) (latitudeFrameAt (x n)) p₀ (fun _ => 1) D ∂bankLaw n μ) atTop (𝓝 (0:ℝ))) :
    Tendsto (fun n => ∫ D,amplitudeNormError μ β J δ q₁ q₂ q
      (x n) (latitudeFrameAt (x n)) p₀ (fun _ => 1) D ∂bankLaw n μ) atTop (𝓝 (0:ℝ)) := by
  exact squeeze_zero (fun n => integral_nonneg fun D => sq_nonneg _)
    (fun n => amplitudeNormError_expectation_le_pairError μ β J δ q₁ q₂ hq
      (x n) (latitudeFrameAt (x n)) p₀ (fun _ => 1)) hPair

/-- The genuine actual pressure contact, upper and latitude inputs close
both physical overlap moment limits and the actual weighted pair variance.
The statement records exactly which analytic evidence is consumed. -/
theorem amplitudePhysicalMoments_and_pairError_tendsto_of_contact_upper_localization
    (μ : FiniteMixture) {β δ q₁ q₂ ρ : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi<β)
    (hβs : β<Thresholds.staticThreshold μ.xi) (hc : IsAdmissibleCollar μ β q₁ q₂)
    (hδ : 0≤δ) (p₀ : Degree μ.maxDegree) (hp₀ : 0 < mixtureCoefficients μ p₀)
    (hqρ : Thresholds.qStar μ.xi β≤ρ) (hρ : ρ<1)
    (x : (n : ℕ) → Vector (n+1)) (hx : ∀ n,‖x n‖^2=((n+1:ℕ):ℝ))
    (hTouch : Tendsto (fun n => amplitudeExpectedPressure μ β (plantedCoreCost μ β) δ q₁ q₂
      (x n) (latitudeFrameAt (x n)) p₀ (fun _ => 1)) atTop
      (𝓝 (β^2*μ.xi 1/2-plantedCoreCost μ β)))
    (hUpper : ∀ k : Fin 2,∀ τ∈Ioo (-1/2:ℝ) (1/2),∀ ε : ℝ,0<ε → ∀ᶠ n : ℕ in atTop,
      amplitudeExpectedPressure μ β (plantedCoreCost μ β) δ q₁ q₂
        (x n) (latitudeFrameAt (x n)) p₀ (amplitudeAt k τ)≤
      weightedAmplitudeTrialEnvelope μ β δ q₁ q₂ p₀ k ρ
        ((μ.qStar_solves_plateau hβ).1.1.le.trans hqρ) hρ τ+ε)
    (hLatitude : Tendsto (fun n => amplitudeLatitudeL1 μ β (plantedCoreCost μ β) δ q₁ q₂
      (Thresholds.qStar μ.xi β) (x n) (latitudeFrameAt (x n)) p₀ (fun _ => 1)) atTop (𝓝 (0:ℝ))) :
    Tendsto (fun n => amplitudePhysicalOverlapFirst μ β (plantedCoreCost μ β) δ q₁ q₂
      (x n) (latitudeFrameAt (x n)) p₀ (fun _ => 1)) atTop (𝓝 (Thresholds.qStar μ.xi β)) ∧
    Tendsto (fun n => amplitudePhysicalOverlapSecond μ β (plantedCoreCost μ β) δ q₁ q₂
      (x n) (latitudeFrameAt (x n)) p₀ (fun _ => 1)) atTop (𝓝 ((Thresholds.qStar μ.xi β)^2)) ∧
    Tendsto (fun n => ∫ D,amplitudePairError μ β (plantedCoreCost μ β) δ q₁ q₂
      (Thresholds.qStar μ.xi β) (x n) (latitudeFrameAt (x n)) p₀ (fun _ => 1) D ∂bankLaw n μ)
      atTop (𝓝 (0:ℝ)) := by
  apply amplitudePhysicalMoments_and_pairError_tendsto_of_derivatives_localization μ
    (μ.dynamicalThreshold_pos.trans hβ).ne' (plantedCoreCost μ β) δ q₁ q₂ p₀ hp₀
    (μ.qStar_solves_plateau hβ).1 x hx hLatitude
  intro k
  have hh := amplitudePressureDerivative_tendsto_of_contact_upper μ hβ hβs hc hδ p₀ k hqρ hρ x hTouch (hUpper k)
  rwa [amplitudeSourceDerivativeTarget_eq_diracShift μ β p₀ k (μ.qStar_solves_plateau hβ).1.1.le] at hh

/-- For every actual finite mixture the genuine internal mean lower closes
pressure contact. Thus only the actual nearby envelope upper and the actual
latitude localization remain as analytic inputs for physical moments. -/
theorem general_amplitudePhysicalMoments_and_pairError_tendsto_of_upper_localization
    (μ : FiniteMixture) {β δ q₁ q₂ ρ : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi<β)
    (hβs : β<Thresholds.staticThreshold μ.xi) (hc : IsAdmissibleCollar μ β q₁ q₂)
    (hδ : 0≤δ) (p₀ : Degree μ.maxDegree) (hp₀ : 0 < mixtureCoefficients μ p₀)
    (hqρ : Thresholds.qStar μ.xi β≤ρ) (hρ : ρ<1)
    (x : (n : ℕ) → Vector (n+1)) (hx : ∀ n,‖x n‖^2=((n+1:ℕ):ℝ))
    (hUpper : ∀ k : Fin 2,∀ τ∈Ioo (-1/2:ℝ) (1/2),∀ ε : ℝ,0<ε → ∀ᶠ n : ℕ in atTop,
      amplitudeExpectedPressure μ β (plantedCoreCost μ β) δ q₁ q₂
        (x n) (latitudeFrameAt (x n)) p₀ (amplitudeAt k τ)≤
      weightedAmplitudeTrialEnvelope μ β δ q₁ q₂ p₀ k ρ
        ((μ.qStar_solves_plateau hβ).1.1.le.trans hqρ) hρ τ+ε)
    (hLatitude : Tendsto (fun n => amplitudeLatitudeL1 μ β (plantedCoreCost μ β) δ q₁ q₂
      (Thresholds.qStar μ.xi β) (x n) (latitudeFrameAt (x n)) p₀ (fun _ => 1)) atTop (𝓝 (0:ℝ))) :
    Tendsto (fun n => amplitudePhysicalOverlapFirst μ β (plantedCoreCost μ β) δ q₁ q₂
      (x n) (latitudeFrameAt (x n)) p₀ (fun _ => 1)) atTop (𝓝 (Thresholds.qStar μ.xi β)) ∧
    Tendsto (fun n => amplitudePhysicalOverlapSecond μ β (plantedCoreCost μ β) δ q₁ q₂
      (x n) (latitudeFrameAt (x n)) p₀ (fun _ => 1)) atTop (𝓝 ((Thresholds.qStar μ.xi β)^2)) ∧
    Tendsto (fun n => ∫ D,amplitudePairError μ β (plantedCoreCost μ β) δ q₁ q₂
      (Thresholds.qStar μ.xi β) (x n) (latitudeFrameAt (x n)) p₀ (fun _ => 1) D ∂bankLaw n μ)
      atTop (𝓝 (0:ℝ)) := by
  apply amplitudePhysicalMoments_and_pairError_tendsto_of_derivatives_localization μ
    (μ.dynamicalThreshold_pos.trans hβ).ne' (plantedCoreCost μ β) δ q₁ q₂ p₀ hp₀
    (μ.qStar_solves_plateau hβ).1 x hx hLatitude
  intro k
  have hh := general_amplitudePressureDerivative_tendsto_of_upper μ hβ hβs hc hδ p₀ k hqρ hρ x
    (by intro n;simpa only [Nat.cast_add,Nat.cast_one] using hx n) (hUpper k)
  rwa [amplitudeSourceDerivativeTarget_eq_diracShift μ β p₀ k (μ.qStar_solves_plateau hβ).1.1.le] at hh

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
