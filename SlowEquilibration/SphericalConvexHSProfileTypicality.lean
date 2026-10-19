-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalConvexPlantedProfile
public import SlowEquilibration.PlantedTrialGeometry

@[expose] public section

/-!
# Genuine planted far-overlap profile typicality for convex covariances

Below the true static threshold, the actual sampled planted latitude profile
has a strict annealed gap at every overlap outside any fixed neighborhood of
zero, except on an exponentially small event. The proof combines the actual
compact-latitude estimate, actual signed mean reflection, the genuine Gaussian
regularity event, and the proved scalar strict-RS gap.
-/

noncomputable section
namespace SlowEquilibration.SphericalModel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators ENNReal

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual Huang--Sellke far-overlap profile gap, proved rather than
assumed, for every finite mixture with convex covariance below its static threshold. -/
theorem convex_planted_far_profile_eventually (μ : FiniteMixture)
    (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi) {β δ : ℝ}
    (hβ : 0 < β) (hβs : β < Thresholds.staticThreshold μ.xi) (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    ∃ η γ : ℝ, 0 < η ∧ 0 < γ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (u : Vector (n+1)), ‖u‖^2=((n+1 : ℕ) : ℝ) →
      ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)), (∀ x, inner ℝ (e x) u=0) →
        disorderLaw (n+1) μ.maxDegree {J | ∃ q ∈ Ioo (-1 : ℝ) 1,
          δ ≤ |q| ∧ β^2*μ.xi 1/2-η < plantedLatitudeProfile n μ β u e q J} ≤
            ENNReal.ofReal (Real.exp (-γ*((n+1 : ℕ) : ℝ))) := by
  let A : ℝ := β^2*μ.xi 1/2
  obtain ⟨ρ,hρ,hpole⟩ := plantedLatitudeProfile_signed_pole_event μ hβ.le (A-1) δ hδ
  obtain ⟨η₀,hη₀,hgap⟩ := exists_uniform_plantedProfileTrial_gap μ hβ.le hβs hδ.1 hρ.1.le hρ.2
  let η : ℝ := min (η₀/2) 1
  have hη : 0 < η := lt_min (half_pos hη₀) zero_lt_one
  obtain ⟨γ₀,hγ₀,hcompact⟩ := convex_plantedLatitudeProfile_eventually_uniform_upper μ hconv hβ
    ⟨hδ.1.trans hρ.1,hρ.2⟩ (half_pos hη₀)
  obtain ⟨γ,hγ,htail⟩ := latitude_polynomial_tail_eventually_le 0 hγ₀
  refine ⟨η,γ,hη,hγ,?_⟩
  filter_upwards [hcompact,htail,eventually_ge_atTop 5] with n hcompact htail hn
  intro u hu e he
  let E : Set (Disorder (n+1) μ.maxDegree) := {J | ∃ q ∈ Icc (-ρ) ρ,
    plantedProfileTrial μ β |q|+η₀/2 ≤ plantedLatitudeProfile n μ β u e q J}
  have hsub : {J : Disorder (n+1) μ.maxDegree | ∃ q ∈ Ioo (-1 : ℝ) 1,
      δ ≤ |q| ∧ A-η < plantedLatitudeProfile n μ β u e q J} ⊆ regularDisorderᶜ ∪ E := by
    rintro J ⟨q,hq,hδq,hJ⟩
    by_cases hreg : J ∈ regularDisorder
    · right
      by_contra hbad
      have habs : |q| < 1 := abs_lt.mpr hq
      by_cases hqρ : |q| ≤ ρ
      · have hgood : plantedLatitudeProfile n μ β u e q J < plantedProfileTrial μ β |q|+η₀/2 := by
          apply lt_of_not_ge
          intro hf
          exact hbad ⟨q,abs_le.mp hqρ,hf⟩
        have hg := hgap |q| ⟨hδq,hqρ⟩
        have hηle : η ≤ η₀/2 := min_le_left _ _
        change _ ≤ A-η₀ at hg
        linarith
      · have hp := (hpole n hn).2 J hreg u hu e he q ⟨(lt_of_not_ge hqρ).le,habs⟩
        have hηle : η ≤ 1 := min_le_right _ _
        linarith
    · exact Or.inl hreg
  have hreg : disorderLaw (n+1) μ.maxDegree (regularDisorder (N := n+1) (P := μ.maxDegree))ᶜ ≤
      ENNReal.ofReal (Real.exp (-((n+1 : ℕ) : ℝ))) := by
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    exact (hpole n hn).1
  have hcomp : disorderLaw (n+1) μ.maxDegree E ≤
      ENNReal.ofReal (Real.exp (-γ₀*((n+1 : ℕ) : ℝ))) := hcompact u hu e he
  apply ((measure_mono hsub).trans (measure_union_le _ _)).trans
  apply (add_le_add hreg hcomp).trans
  rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hexp : Real.exp (-((n+1 : ℕ) : ℝ)) ≤ Real.exp (-((n+1 : ℕ) : ℝ)/2) := by
    apply Real.exp_le_exp.mpr
    have hN : (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by positivity
    linarith
  simp only [pow_zero] at htail
  have hp := Real.exp_pos (-γ₀*((n+1 : ℕ) : ℝ))
  linarith

end SlowEquilibration.SphericalModel
