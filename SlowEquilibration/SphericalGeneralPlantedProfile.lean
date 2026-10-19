-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGeneralLatitudeMean
public import SlowEquilibration.SphericalConvexPlantedProfile

@[expose] public section

/-! # Actual planted compact latitude estimates for arbitrary finite mixtures

The genuine general Guerra upper and exact planted shift control every
latitude bounded away from zero and the poles. Signed latitudes use the
proved mean reflection and continuum Gaussian concentration.
-/
namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators ENNReal
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem general_plantedLatitudeQuenchedPressure_eventually_uniform_upper
    (μ : FiniteMixture) {β δ ρ ε : ℝ} (hβ : 0 < β)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ : ρ < 1) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ q ∈ Icc δ ρ, ∀ (u : Vector (n+1)),
      ‖u‖^2=((n+1 : ℕ) : ℝ) → ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)),
      (∀ x, inner ℝ (e x) u=0) →
      plantedLatitudeQuenchedPressure n μ β u e q ≤
        (β^2*(μ.xi 1+μ.xi q)+q-Real.log (1+q))/2+ε := by
  filter_upwards [general_latitudeQuenchedPressure_eventually_uniform_upper μ β
    hδ hδρ hρ hε, eventually_ge_atTop 1] with n hn hdim
  intro q hq u hu e he
  have hh := hn q hq u hu e he
  rw [plantedLatitudeQuenchedPressure_eq hdim μ hβ u hu e he
    (abs_le.mpr ⟨by linarith [hq.1], hq.2.trans hρ.le⟩)]
  unfold latitudePressureTrial at hh
  linarith

theorem general_plantedLatitudeMeanProfile_eventually_uniform_upper
    (μ : FiniteMixture) {β δ ρ ε : ℝ} (hβ : 0 < β)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ : ρ < 1) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ q ∈ Icc δ ρ, ∀ (u : Vector (n+1)),
      ‖u‖^2=((n+1 : ℕ) : ℝ) → ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)),
      (∀ x, inner ℝ (e x) u=0) →
      plantedLatitudeMeanProfile n μ β u e q ≤ plantedProfileTrial μ β q+ε := by
  have hsmall := (latitudeEntropyError_tendsto ρ).eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [general_plantedLatitudeQuenchedPressure_eventually_uniform_upper μ
    hβ hδ hδρ hρ (half_pos hε), hsmall, eventually_ge_atTop 2] with n hmean hsmall hn
  intro q hq u hu e he
  have hp := plantedLatitudeMeanProfile_le hn μ β u e ⟨hδ.trans_le hδρ,hρ⟩
    ⟨hδ.le.trans hq.1,hq.2⟩ (hmean q hq u hu e he)
  linarith

theorem general_plantedLatitudeProfile_eventually_uniform_upper
    (μ : FiniteMixture)
    {β δ ρ ε : ℝ} (hβ : 0 < β) (hδ : 0 < δ)
    (hδρ : δ ≤ ρ) (hρ : ρ < 1) (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (u : Vector (n+1)), ‖u‖^2=((n+1 : ℕ) : ℝ) →
      ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)), (∀ x, inner ℝ (e x) u=0) →
        disorderLaw (n+1) μ.maxDegree {J | ∃ q ∈ Icc (-ρ) ρ, δ ≤ |q| ∧
          plantedProfileTrial μ β |q|+ε ≤ plantedLatitudeProfile n μ β u e q J} ≤
          ENNReal.ofReal (Real.exp (-γ*((n+1 : ℕ) : ℝ))) := by
  obtain ⟨γ,hγ,hconc⟩ := latitude_uniform_concentration_eventually
    (mixtureCoefficients μ) (mixtureCoefficients_nonnegative μ)
    (by rw [covariancePolynomial_mixture]; exact μ.xi_pos (by norm_num)) hβ (half_pos hε)
  refine ⟨γ,hγ,?_⟩
  filter_upwards [hconc,general_plantedLatitudeMeanProfile_eventually_uniform_upper μ
    hβ hδ hδρ hρ (half_pos hε), eventually_ge_atTop 1] with n hconc hmean hn
  intro u hu e he
  apply (measure_mono ?_).trans (hconc (-ρ) ρ (by linarith [hρ]) hρ.le
    (by linarith [hδ.trans_le hδρ]) u hu e he)
  rintro J ⟨q,hq,hδq,hJ⟩
  refine ⟨q,hq,?_⟩
  have hqa : |q| ≤ 1 := abs_le.mpr ⟨by linarith [hq.1,hρ],hq.2.trans hρ.le⟩
  have hqabs : |q| ∈ Icc δ ρ := ⟨hδq,abs_le.mpr hq⟩
  rw [plantedLatitudeProfile_centered hn μ hβ u hu e he hqa] at hJ
  have hm := (plantedLatitudeMeanProfile_le_abs hn μ hβ u hu e he hqa).trans
    (hmean |q| hqabs u hu e he)
  have hN : 0 < ((n+1 : ℕ) : ℝ) := by positivity
  have hf : ε/2 ≤ latitudeCenteredLogPartition (mixtureCoefficients μ) β u e q J/
      ((n+1 : ℕ) : ℝ) := by linarith
  exact ((le_div_iff₀ hN).mp hf).trans (le_abs_self _)

end
end SlowEquilibration.SphericalModel
