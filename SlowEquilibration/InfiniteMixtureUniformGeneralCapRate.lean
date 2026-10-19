-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalGeneralQuantitativeReplicaBound
public import SlowEquilibration.InfiniteMixtureUniformStaticGap
public import SlowEquilibration.InfiniteMixtureCutoffThreshold

/-! A fixed positive cap exponent for every finite cutoff and every
positive temperature bounded by one strict infinite-mixture static threshold.
Only the eventual dimension is allowed to depend on the cutoff and temperature. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.InfiniteMixture
open MeasureTheory ProbabilityTheory SphericalModel Set Filter
open scoped Topology
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem exists_uniform_finiteCutoff_cap_rate (μ : InfiniteMixture)
    {β₀ s : ℝ}
    (hβ₀ : 0<β₀) (hβs : β₀<Thresholds.staticThreshold μ.xi)
    (hs : s∈Ioo (0:ℝ) 1) :
    ∃ c : ℝ,0<c ∧ ∀ P (hP : ∃ p,p≤P ∧ 0<μ.coeff p),
      ∀ β : ℝ,0<β → β≤β₀ → ∀ᶠ N : ℕ in atTop,
        ∃ Ω : Set (Disorder N (μ.finiteCutoff P hP).maxDegree),MeasurableSet Ω ∧
          (disorderLaw N (μ.finiteCutoff P hP).maxDegree).real Ωᶜ≤Real.exp (-c*N) ∧
          ∀ J∈Ω,∀ v : Vector N,‖v‖^2=(N:ℝ) →
            (gibbsLaw N β (fieldOfMixture (μ.finiteCutoff P hP) J)).real (cap v s)≤Real.exp (-c*N) := by
  have hδ : s^2/2∈Ioo (0:ℝ) 1 := by
    constructor
    · exact div_pos (sq_pos_of_pos hs.1) (by norm_num)
    · nlinarith [sq_nonneg (1-s),hs.1,hs.2]
  obtain ⟨η,hη,hgap⟩ := μ.exists_uniform_finiteCutoff_trial_gap hβ₀ hβs hδ
  let B := β₀^2*μ.xi 1+1
  have hx : 0≤μ.xi 1 := tsum_nonneg fun p => by simp [μ.nonneg p]
  have hB : 0<B := by dsimp [B]; positivity
  refine ⟨commonReplicaRate η B/4,by have := commonReplicaRate_pos hη hB; positivity,?_⟩
  intro P hP β hβ hβle
  apply general_uniform_cap_mass_explicit (μ.finiteCutoff P hP) hβ
    ((hβle.trans_lt hβs).trans_le (μ.staticThreshold_le_finiteCutoff P hP)) hs hη hB
  · have hv := μ.finiteCutoff_temperature_variance_le P hP hβ.le hβle
    dsimp [B]
    linarith
  · exact hgap P hP β hβ.le hβle

end SlowEquilibration.InfiniteMixture
