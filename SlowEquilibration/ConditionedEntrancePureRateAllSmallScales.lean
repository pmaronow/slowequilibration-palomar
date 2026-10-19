-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureRateAtScale

/-! The original proper-pure source cutoff entrance rate at every sufficiently
small latitude radius, with the threshold chosen before the radius. -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SlowEquilibration.SphericalModel
open SlowEquilibration.SphericalOverlapExponential
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false

theorem actual_pureSource_axis_averaged_cap_hit_source_rate_all_small_scales
    (d : ℕ) (hd : 4 ≤ d) (c : ℝ) (hc : 0 < c)
    {Q B β : ℝ} (hQ : 0 < Q) (hB : 0 ≤ B) (hβ : 0 ≤ β)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (hχb : ∀ s, |χ s| ≤ 1) (hχR : ∀ s, 2 < |s| → χ s = 0) :
    ∃ aStar : ℝ, 0 < aStar ∧
      ∀ {a : ℝ}, 0 < a → a ≤ aStar →
        ∃ (γ decay C : ℝ), 0 < γ ∧ 0 < decay ∧ 0 < C ∧
          ∀ᶠ n : ℕ in atTop,
            ∀ (e : ℝ), |e| ≤ B →
              (∫ J, pureAxisAveragedCapHitProbability d (by omega) c hc Q
                (2*a) χ hχ β (exponentialGridHorizon γ (n+1)) e J
                ∂disorderLaw (n+1) (FiniteMixture.pure d (by omega : 2 ≤ d) c hc).maxDegree) ≤
              C*(((n+1 : ℕ) : ℝ)^(1-((FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree : ℝ)/2)+
                ((n+1 : ℕ) : ℝ)^(3-((FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree : ℝ)))+
                Real.exp (-decay*((n+1 : ℕ) : ℝ)) := by
  let a₁ := EntranceLatitudeTangentObservable.sourceCutoffMomentScale (FiniteMixture.pure d (by omega : 2 ≤ d) c hc) Q B (2*β)
  let a₂ := 1/(128*(1+β*
    pureCutoffEnergyConstant d (by omega) c hc Q B))
  let aStar := min a₁ a₂ / 2
  have ha₁ : 0 < a₁ :=
    EntranceLatitudeTangentObservable.sourceCutoffMomentScale_pos (FiniteMixture.pure d (by omega : 2 ≤ d) c hc) Q B (2*β)
  have ha₂ : 0 < a₂ := by
    have hC := pureCutoffEnergyConstant_nonneg d (by omega) c hc Q B hB
    dsimp only [a₂]
    positivity
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
      EntranceLatitudeTangentObservable.sourceCutoffMomentScale (FiniteMixture.pure d (by omega : 2 ≤ d) c hc) Q B (2*β) :=
    hαle.trans (min_le_left a₁ a₂)
  have hαenergy : 2*a ≤
      1/(128*(1+β*
        pureCutoffEnergyConstant d (by omega) c hc Q B)) :=
    hαle.trans (min_le_right a₁ a₂)
  exact actual_pureSource_axis_averaged_cap_hit_source_rate_at_scale
    d hd c hc hQ hB hβ hα hαmoment hαenergy χ hχ hχb hχR

end SlowEquilibration.ConditionedEntrance
