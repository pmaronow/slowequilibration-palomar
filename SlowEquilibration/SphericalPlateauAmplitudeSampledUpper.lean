-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeConcentration
public import SlowEquilibration.SphericalPlateauAmplitudeDiracUpper

@[expose] public section

/-! # Genuine sampled uniform Dirac upper for the source amplitude bank

The actual quenched mean bound and genuine bank continuum concentration
combine without a supplied pressure bound, positivity event or regularity
premise. Every reference axis is quantified after a common dimension threshold.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel
open scoped Topology ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal sampled normalized log partition of the perturbed bank. -/
def amplitudeLatitudeSampledPressure {n : ℕ} (μ : FiniteMixture) (β : ℝ)
    (x : Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (r : ℝ)
    (D : BankDisorder n μ) : ℝ :=
  amplitudeLatitudeLogPartition μ β x p₀ s r D/((n+1 : ℕ) : ℝ)

/-- Uniform sampled upper on any fixed signed latitude window avoiding zero,
with an exponential failure probability under the actual independent bank law. -/
theorem amplitudeLatitudeSampledPressure_eventually_uniform_dirac_upper
    (μ : FiniteMixture) {β : ℝ} (hβ : 0<β) (p₀ : Degree μ.maxDegree)
    {δ ρ ε : ℝ} (hδ : 0<δ) (hδρ : δ≤ρ) (hρ : ρ<1) (hε : 0<ε) :
    ∃ γ : ℝ,0<γ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (s : Fin 2 → ℝ),(∀ j,|s j|≤2) →
      ∀ (x : Vector (n+1)),‖x‖^2=((n+1 : ℕ) : ℝ) →
        bankLaw n μ {D | ∃ r : ℝ,|r|∈Icc δ ρ ∧
          amplitudeDiracTrial μ β p₀ s r+ε<amplitudeLatitudeSampledPressure μ β x p₀ s r D}≤
          ENNReal.ofReal (Real.exp (-γ*((n+1 : ℕ) : ℝ))) := by
  obtain ⟨γ,hγ,hconc⟩ := amplitudeLatitude_uniform_concentration_eventually μ hβ
    (show 0<ε/2 by positivity) p₀
  have hmean := amplitudeLatitudeQuenchedPressure_eventually_uniform_dirac_upper μ β p₀
    hδ hδρ hρ (show 0<ε/2 by positivity)
  refine ⟨γ,hγ,?_⟩
  filter_upwards [hconc,hmean] with n hconc hmean
  intro s hs x hx
  have hρ0 : 0≤ρ := hδ.le.trans hδρ
  have hconc' := hconc s hs (-ρ) ρ (by linarith) hρ.le (by linarith) x hx
  apply (measure_mono ?_).trans hconc'
  rintro D ⟨r,hr,hD⟩
  refine ⟨r,abs_le.mp hr.2,?_⟩
  have hN : 0<((n+1 : ℕ) : ℝ) := by positivity
  have hM := hmean s hs r hr x hx (latitudeFrameAt x) (latitudeFrameAt_orthogonal x hx)
  change (∫ E,amplitudeLatitudeLogPartition μ β x p₀ s r E ∂bankLaw n μ)/((n+1 : ℕ) : ℝ)≤
    amplitudeDiracTrial μ β p₀ s r+ε/2 at hM
  have hM' := (div_le_iff₀ hN).mp hM
  have hD' := (lt_div_iff₀ hN).mp hD
  have hcenter : (ε/2)*((n+1 : ℕ) : ℝ)≤amplitudeLatitudeCenteredLogPartition μ β x p₀ s r D := by
    unfold amplitudeLatitudeCenteredLogPartition
    nlinarith
  exact hcenter.trans (le_abs_self _)

/-- The original source direction has exactly its stated trial and
τ(2+τ) selected-block correction, for both latitude signs. -/
theorem amplitudeLatitudeSampledPressure_at_eventually_uniform_upper
    (μ : FiniteMixture) {β : ℝ} (hβ : 0<β) (p₀ : Degree μ.maxDegree)
    {δ ρ ε : ℝ} (hδ : 0<δ) (hδρ : δ≤ρ) (hρ : ρ<1) (hε : 0<ε) :
    ∃ γ : ℝ,0<γ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (k : Fin 2) (τ : ℝ),τ∈Icc (-1/2 : ℝ) (1/2) →
      ∀ (x : Vector (n+1)),‖x‖^2=((n+1 : ℕ) : ℝ) →
        bankLaw n μ {D | ∃ r : ℝ,|r|∈Icc δ ρ ∧
          latitudePressureTrial μ β |r|+τ*(2+τ)*amplitudeDiracShiftCoefficient μ β p₀ k r+ε<
            amplitudeLatitudeSampledPressure μ β x p₀ (amplitudeAt k τ) r D}≤
          ENNReal.ofReal (Real.exp (-γ*((n+1 : ℕ) : ℝ))) := by
  obtain ⟨γ,hγ,hupper⟩ := amplitudeLatitudeSampledPressure_eventually_uniform_dirac_upper μ hβ p₀ hδ hδρ hρ hε
  refine ⟨γ,hγ,?_⟩
  filter_upwards [hupper] with n hupper
  intro k τ hτ x hx
  have hs : ∀ j,|amplitudeAt k τ j|≤2 := by
    intro j
    unfold amplitudeAt
    split_ifs
    · exact abs_le.mpr ⟨by linarith [hτ.1],by linarith [hτ.2]⟩
    · norm_num
  apply (measure_mono ?_).trans (hupper (amplitudeAt k τ) hs x hx)
  rintro D ⟨r,hr,hD⟩
  refine ⟨r,hr,?_⟩
  rw [amplitudeDiracTrial_at,amplitudeDiracTrial_one μ β p₀ (hr.2.trans_lt hρ)]
  exact hD

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
