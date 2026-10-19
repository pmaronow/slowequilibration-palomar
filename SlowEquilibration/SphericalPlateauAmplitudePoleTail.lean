-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeRestrictedAnnealed

@[expose] public section

/-! # Genuine actual polar weighted-partition tail for the source bank -/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalBarycenter
open scoped Topology ENNReal
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

theorem amplitudeRestrictedPartition_tail_le (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (hK : 0 ≤ sourceK J δ) (x : Vector (n+1)) (hx : ‖x‖^2=((n+1:ℕ):ℝ))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (hs : ∀ j,|s j|≤2)
    (E : Set (Vector (n+1))) (B : ℝ) (hB : 0<B) :
    (bankLaw n μ).real {D | B≤amplitudeRestrictedPartition μ β J δ q₁ q₂ x p₀ s E D}≤
      Real.exp (3*β^2*((n+1:ℕ):ℝ)*μ.xi 1)*(sphereLaw (n+1)).real E/B := by
  have hm := amplitudeRestrictedPartition_measurable μ β J δ q₁ q₂ x p₀ s E
  have hTail := meas_ge_le_lintegral_div (hm.ennreal_ofReal.aemeasurable (μ := bankLaw n μ))
    ((ENNReal.ofReal_pos.mpr hB).ne') ENNReal.ofReal_ne_top
  have hSub : {D | B≤amplitudeRestrictedPartition μ β J δ q₁ q₂ x p₀ s E D}⊆
      {D | ENNReal.ofReal B≤ENNReal.ofReal (amplitudeRestrictedPartition μ β J δ q₁ q₂ x p₀ s E D)} :=
    fun D hD => ENNReal.ofReal_le_ofReal hD
  have hAnnealed := amplitudeRestrictedPartition_lintegral_le μ β J δ q₁ q₂ hK x hx p₀ s hs E
  have hLe := ((measure_mono hSub).trans hTail).trans
    (ENNReal.div_le_div_right hAnnealed (ENNReal.ofReal B))
  have hr := ENNReal.toReal_mono (by finiteness) hLe
  simpa only [Measure.real,ENNReal.toReal_div,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_nonneg _),ENNReal.toReal_ofReal hB.le] using hr

/-- Any finite target exponent has a fixed polar cutoff above the requested
interior latitude, with an exponential actual bank failure bound. -/
theorem exists_amplitudePolarPartition_tail (μ : FiniteMixture) (β J δ q₁ q₂ M : ℝ)
    (hK : 0 ≤ sourceK J δ) {a : ℝ} (ha : a∈Ico (0:ℝ) 1) :
    ∃ ρ : ℝ,a<ρ ∧ ρ<1 ∧ 0<ρ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ x : Vector (n+1),‖x‖^2=((n+1:ℕ):ℝ) →
      ∀ p₀ : Degree μ.maxDegree,∀ s : Fin 2 → ℝ,(∀ j,|s j|≤2) →
        (bankLaw n μ).real {D | Real.exp (((n+1:ℕ):ℝ)*M)≤
          amplitudeRestrictedPartition μ β J δ q₁ q₂ x p₀ s (poleRegion x ρ) D}≤
          Real.exp (-((n+1:ℕ):ℝ)) := by
  let K := max (3*β^2*μ.xi 1-M+1) 1
  have hKpos : 0<K := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _)
  obtain ⟨ρ,haρ,hρ,hρ0,hTail⟩ := exists_uniform_sphere_pole_mass_rate ha hKpos
  refine ⟨ρ,haρ,hρ,hρ0,?_⟩
  filter_upwards [hTail] with n hn
  intro x hx p₀ s hs
  have hb := amplitudeRestrictedPartition_tail_le μ β J δ q₁ q₂ hK x hx p₀ s hs
    (poleRegion x ρ) (Real.exp (((n+1:ℕ):ℝ)*M)) (Real.exp_pos _)
  apply hb.trans
  have hMass := hn x hx
  have hmul := mul_le_mul_of_nonneg_left hMass
    (Real.exp_nonneg (3*β^2*((n+1:ℕ):ℝ)*μ.xi 1))
  have hdiv := div_le_div_of_nonneg_right hmul (Real.exp_nonneg (((n+1:ℕ):ℝ)*M))
  apply hdiv.trans
  rw [← Real.exp_add,← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  have hRate : 3*β^2*μ.xi 1-M+1≤K := le_max_left _ _
  have hNp : 0≤((n+1:ℕ):ℝ) := by positivity
  nlinarith

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
