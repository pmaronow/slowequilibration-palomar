-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeWeightedConcentration

@[expose] public section

/-! # Actual sampled weighted upper bounds imply actual mean upper bounds

This probability connector consumes a bound on the literal sampled source
partition and the internally proved concentration about its actual bank mean.
The dimension threshold precedes every source direction and reference axis.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

/-- Two actual probability tails whose bounds sum to less than one force
the actual expected pressure below the sampled target plus both tolerances. -/
theorem amplitudeExpectedPressure_le_of_sampled_upper_tails
    (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ) (x : Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (G η t a b : ℝ)
    (hupper : (bankLaw n μ).real {D | G+η<
      Real.log (amplitudePartition μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s D)/((n+1 : ℕ) : ℝ)}≤a)
    (hcenter : (bankLaw n μ).real {D | t≤
      |Real.log (amplitudePartition μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s D)/((n+1 : ℕ) : ℝ)-
        amplitudeExpectedPressure μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s|}≤b)
    (hab : a+b<1) :
    amplitudeExpectedPressure μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s≤G+η+t := by
  by_contra hmean
  have hmean' := lt_of_not_ge hmean
  have hsub : (univ : Set (BankDisorder n μ))⊆
      {D | G+η<Real.log (amplitudePartition μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s D)/((n+1 : ℕ) : ℝ)}∪
      {D | t≤|Real.log (amplitudePartition μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s D)/((n+1 : ℕ) : ℝ)-
        amplitudeExpectedPressure μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s|} := by
    intro D _
    by_cases hD : G+η<Real.log (amplitudePartition μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s D)/((n+1 : ℕ) : ℝ)
    · exact Or.inl hD
    · right
      change t≤|Real.log (amplitudePartition μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s D)/((n+1 : ℕ) : ℝ)-
        amplitudeExpectedPressure μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s|
      have hD' := le_of_not_gt hD
      have hh := neg_le_abs (Real.log (amplitudePartition μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s D)/((n+1 : ℕ) : ℝ)-
        amplitudeExpectedPressure μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s)
      linarith
  have hh := ((measureReal_mono hsub).trans (measureReal_union_le (μ := bankLaw n μ) _ _)).trans
    (add_le_add hupper hcenter)
  simp only [measureReal_def,measure_univ,ENNReal.toReal_one] at hh
  linarith

/-- The genuine centered concentration converts every uniformly exponential
sampled upper for the literal amplitude partition into a mean upper.
The sampled probability premise is an explicit connector input; it will be
instantiated by the physical coarea and pole estimates. -/
theorem amplitudeExpectedPressure_eventually_upper_of_sampled_upper
    (μ : FiniteMixture) {β : ℝ} (hβ : 0<β) (J δ q₁ q₂ : ℝ) (p₀ : Degree μ.maxDegree)
    (G : Fin 2 → ℝ → ℝ)
    (hsample : ∀ η : ℝ,0<η → ∃ γ : ℝ,0<γ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (k : Fin 2) (τ : ℝ),τ∈Icc (-1/2 : ℝ) (1/2) →
      ∀ (x : Vector (n+1)),‖x‖^2=((n+1 : ℕ) : ℝ) →
        (bankLaw n μ).real {D | G k τ+η<
          Real.log (amplitudePartition μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ (amplitudeAt k τ) D)/((n+1 : ℕ) : ℝ)}≤
          2*Real.exp (-γ*((n+1 : ℕ) : ℝ)))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,∀ (k : Fin 2) (τ : ℝ),τ∈Icc (-1/2 : ℝ) (1/2) →
      ∀ (x : Vector (n+1)),‖x‖^2=((n+1 : ℕ) : ℝ) →
        amplitudeExpectedPressure μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ (amplitudeAt k τ)≤G k τ+ε := by
  obtain ⟨γs,hγs,hsample⟩ := hsample (ε/2) (by positivity)
  obtain ⟨γc,hγc,hconc⟩ := amplitudeWeightedPressure_concentration_eventually μ hβ
    (show 0<ε/2 by positivity) p₀
  have hN : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hexp (γ : ℝ) (hγ : 0<γ) :
      Tendsto (fun n : ℕ => Real.exp (-γ*((n+1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp (hN.const_mul_atTop hγ) using 1
    ext n
    simp only [Function.comp_apply,neg_mul]
  have hsum : Tendsto (fun n : ℕ => 2*Real.exp (-γs*((n+1 : ℕ) : ℝ))+
      Real.exp (-γc*((n+1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_add] using ((hexp γs hγs).const_mul 2).add (hexp γc hγc)
  have hsmall := hsum.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1))
  filter_upwards [hsample,hconc,hsmall] with n hsample hconc hsmall
  intro k τ hτ x hx
  have hs : ∀ j,|amplitudeAt k τ j|≤2 := by
    intro j
    unfold amplitudeAt
    split_ifs
    · exact abs_le.mpr ⟨by linarith [hτ.1],by linarith [hτ.2]⟩
    · norm_num
  have hc := hconc J δ q₁ q₂ (amplitudeAt k τ) hs x hx
  have hcr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hc
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le] at hcr
  have hm := amplitudeExpectedPressure_le_of_sampled_upper_tails μ β J δ q₁ q₂ x p₀ (amplitudeAt k τ)
    (G k τ) (ε/2) (ε/2) _ _ (hsample k τ hτ x hx) hcr hsmall
  convert hm using 1
  ring

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
