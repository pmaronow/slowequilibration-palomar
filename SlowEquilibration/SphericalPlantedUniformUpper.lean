-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeUniformConcentration
public import SlowEquilibration.SphericalPlantedProfile

@[expose] public section

/-!
# The actual planted latitude profile is uniformly bounded by Psi

The true thermodynamic mean estimate and the proved continuum concentration
are combined for the literal planted tensor realization. The failure
probability is exponentially small, uniformly in every deterministic center
and tangent frame, with no concentration or mean asymptotic premise.
-/

noncomputable section
namespace SlowEquilibration.SphericalModel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators ENNReal

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def plantedLatitudeProfile (n : ℕ) (μ : FiniteMixture) (β : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ)
    (J : Disorder (n+1) μ.maxDegree) : ℝ :=
  Real.log (partitionAgainst (latitudeLaw u e q) β
      (field (mixtureCoefficients μ) (J+plantedShift (mixtureCoefficients μ) β u)))/((n+1 : ℕ) : ℝ)+
    ((n-2 : ℕ) : ℝ)/(2*((n+1 : ℕ) : ℝ))*Real.log (1-q^2)

/-- Planting changes only the exact deterministic latitude mean; the
centered random fluctuation remains that of the original tensor field. -/
theorem plantedLatitudeProfile_centered {n : ℕ} (hn : 1 ≤ n)
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x, inner ℝ (e x) u=0)
    {q : ℝ} (hq : |q| ≤ 1) (J : Disorder (n+1) μ.maxDegree) :
    plantedLatitudeProfile n μ β u e q J = plantedLatitudeMeanProfile n μ β u e q+
      latitudeCenteredLogPartition (mixtureCoefficients μ) β u e q J/((n+1 : ℕ) : ℝ) := by
  unfold plantedLatitudeProfile plantedLatitudeMeanProfile
  rw [latitude_logPartition_plantedShift hn _ (mixtureCoefficients_nonnegative μ) β u hu e he hq,
    plantedLatitudeQuenchedPressure_eq hn μ hβ u hu e he hq,covariancePolynomial_mixture]
  unfold latitudeCenteredLogPartition latitudeLogPartition latitudeQuenchedPressure fieldOfMixture
  have hN : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- Actual high-probability planted Psi upper on every compact positive
latitude interval above one half, valid also for odd mixtures. -/
theorem plantedLatitudeProfile_eventually_uniform_upper (μ : FiniteMixture)
    {β ρ ε : ℝ} (hβ : 0 < β) (hρ : ρ ∈ Ioo (1/2 : ℝ) 1) (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (u : Vector (n+1)), ‖u‖^2=((n+1 : ℕ) : ℝ) →
      ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)), (∀ x, inner ℝ (e x) u=0) →
        disorderLaw (n+1) μ.maxDegree {J | ∃ q ∈ Icc (1/2 : ℝ) ρ,
          plantedProfileTrial μ β q+ε ≤ plantedLatitudeProfile n μ β u e q J} ≤
          ENNReal.ofReal (Real.exp (-γ*((n+1 : ℕ) : ℝ))) := by
  obtain ⟨γ,hγ,hconc⟩ := latitude_uniform_concentration_eventually
    (mixtureCoefficients μ) (mixtureCoefficients_nonnegative μ)
    (by rw [covariancePolynomial_mixture]; exact μ.xi_pos (by norm_num)) hβ (half_pos hε)
  refine ⟨γ,hγ,?_⟩
  filter_upwards [hconc,plantedLatitudeMeanProfile_eventually_uniform_upper μ hβ hρ (half_pos hε),
    eventually_ge_atTop 1] with n hconc hmean hn
  intro u hu e he
  apply (measure_mono ?_).trans (hconc (1/2) ρ (by norm_num) hρ.2.le (by linarith [hρ.1]) u hu e he)
  rintro J ⟨q,hq,hJ⟩
  refine ⟨q,hq,?_⟩
  have hqa : |q| ≤ 1 := abs_le.mpr ⟨by linarith [hq.1],hq.2.trans hρ.2.le⟩
  rw [plantedLatitudeProfile_centered hn μ hβ u hu e he hqa] at hJ
  have hm := hmean q hq u hu e he
  have hN : 0 < ((n+1 : ℕ) : ℝ) := by positivity
  have hf : ε/2 ≤ latitudeCenteredLogPartition (mixtureCoefficients μ) β u e q J/((n+1 : ℕ) : ℝ) := by
    linarith
  exact ((le_div_iff₀ hN).mp hf).trans (le_abs_self _)

/-- For even mixtures the same genuine exponential estimate holds down
to latitude zero, as required by the truncated-RS construction. -/
theorem plantedLatitudeProfile_eventually_uniform_upper_of_even (μ : FiniteMixture)
    {β ρ ε : ℝ} (hβ : 0 < β) (heven : ∀ p ∈ μ.coeff.support, Even p)
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (u : Vector (n+1)), ‖u‖^2=((n+1 : ℕ) : ℝ) →
      ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)), (∀ x, inner ℝ (e x) u=0) →
        disorderLaw (n+1) μ.maxDegree {J | ∃ q ∈ Icc (0 : ℝ) ρ,
          plantedProfileTrial μ β q+ε ≤ plantedLatitudeProfile n μ β u e q J} ≤
          ENNReal.ofReal (Real.exp (-γ*((n+1 : ℕ) : ℝ))) := by
  obtain ⟨γ,hγ,hconc⟩ := latitude_uniform_concentration_eventually
    (mixtureCoefficients μ) (mixtureCoefficients_nonnegative μ)
    (by rw [covariancePolynomial_mixture]; exact μ.xi_pos (by norm_num)) hβ (half_pos hε)
  refine ⟨γ,hγ,?_⟩
  filter_upwards [hconc,plantedLatitudeMeanProfile_eventually_uniform_upper_of_even μ hβ heven hρ (half_pos hε),
    eventually_ge_atTop 1] with n hconc hmean hn
  intro u hu e he
  apply (measure_mono ?_).trans (hconc 0 ρ (by norm_num) hρ.2.le hρ.1.le u hu e he)
  rintro J ⟨q,hq,hJ⟩
  refine ⟨q,hq,?_⟩
  have hqa : |q| ≤ 1 := abs_le.mpr ⟨by linarith [hq.1],hq.2.trans hρ.2.le⟩
  rw [plantedLatitudeProfile_centered hn μ hβ u hu e he hqa] at hJ
  have hm := hmean q hq u hu e he
  have hN : 0 < ((n+1 : ℕ) : ℝ) := by positivity
  have hf : ε/2 ≤ latitudeCenteredLogPartition (mixtureCoefficients μ) β u e q J/((n+1 : ℕ) : ℝ) := by
    linarith
  exact ((le_div_iff₀ hN).mp hf).trans (le_abs_self _)

end SlowEquilibration.SphericalModel
