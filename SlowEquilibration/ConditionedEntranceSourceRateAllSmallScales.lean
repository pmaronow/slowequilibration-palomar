-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceRateAtScale

/-! The original mixed-source cutoff entrance rate at every sufficiently
small latitude radius, with the threshold chosen before the radius. -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SlowEquilibration.SphericalModel
open SlowEquilibration.SphericalOverlapExponential
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false

theorem actual_mixedSource_axis_averaged_cap_hit_source_rate_all_small_scales
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree)
    {Q B β : ℝ} (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (hnp : μ.minDegree < μ.maxDegree) (hB : 0 ≤ B) (hβ : 0 ≤ β)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (hχb : ∀ s, |χ s| ≤ 1) (hχR : ∀ s, 2 < |s| → χ s = 0) :
    ∃ aStar : ℝ, 0 < aStar ∧
      ∀ {a : ℝ}, 0 < a → a ≤ aStar →
        ∃ (γ c C : ℝ), 0 < γ ∧ 0 < c ∧ 0 < C ∧
          ∀ᶠ n : ℕ in atTop,
            ∀ (e k : ℝ), |e| ≤ B → |k| ≤ B →
              (∫ J, sourceAxisAveragedCapHitProbability μ Q hQ hnp
                (2*a) χ hχ β (exponentialGridHorizon γ (n+1)) e k J
                ∂disorderLaw (n+1) μ.maxDegree) ≤
              C*(((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)+
                ((n+1 : ℕ) : ℝ)^(3-(μ.minDegree : ℝ)))+
                Real.exp (-c*((n+1 : ℕ) : ℝ)) := by
  let a₁ := EntranceLatitudeTangentObservable.sourceCutoffMomentScale μ Q B (2*β)
  let a₂ := 1/(128*(1+β*
    PhysicalHitting.uniformCutoffEnergyConstant μ Q B B 1 2))
  let aStar := min a₁ a₂ / 2
  have ha₁ : 0 < a₁ :=
    EntranceLatitudeTangentObservable.sourceCutoffMomentScale_pos μ Q B (2*β)
  have ha₂ : 0 < a₂ :=
    PhysicalHitting.uniform_source_cutoff_cap_tail_radius_pos μ hβ hB hB
      (by norm_num : (0 : ℝ) ≤ 2)
  have hstar : 0 < aStar := by
    dsimp only [aStar]
    exact half_pos (lt_min ha₁ ha₂)
  refine ⟨aStar, hstar, ?_⟩
  intro a ha hab
  have hα : 0 < 2*a := by positivity
  have hαle : 2*a ≤ min a₁ a₂ := by
    dsimp only [aStar] at hab
    linarith
  have hαmoment : 2*a ≤
      EntranceLatitudeTangentObservable.sourceCutoffMomentScale μ Q B (2*β) :=
    hαle.trans (min_le_left a₁ a₂)
  have hαenergy : 2*a ≤
      1/(128*(1+β*
        PhysicalHitting.uniformCutoffEnergyConstant μ Q B B 1 2)) :=
    hαle.trans (min_le_right a₁ a₂)
  exact actual_mixedSource_axis_averaged_cap_hit_source_rate_at_scale
    μ hd hQ hQ1 hnp hB hβ hα hαmoment hαenergy χ hχ hχb hχR

end SlowEquilibration.ConditionedEntrance
