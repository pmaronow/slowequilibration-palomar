-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceTrueRateBridge

/-! The unconditional manuscript rate for the uncut physical source
Hamiltonian at each prescribed axis, in the exact probability form used by
the centered critical-point transfer. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalForm SphericalOverlapExponential
open SphericalAging HardSphereDynamics
open scoped NNReal
set_option autoImplicit false
set_option maxHeartbeats 400000

theorem sourceUncut_fixed_axis_cap_hit_source_rate_all_small_scales
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree)
    {Q B β : ℝ} (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (hnp : μ.minDegree < μ.maxDegree) (hB : 0 ≤ B) (hβ : 0 ≤ β) :
    ∃ aStar : ℝ, 0 < aStar ∧
      ∀ {a : ℝ} (_ha : 0 < a), a ≤ aStar →
        ∃ (γ c C : ℝ), 0 < γ ∧ 0 < c ∧ 0 < C ∧
          ∀ᶠ n : ℕ in atTop,
            ∀ (e k : ℝ), |e| ≤ B → |k| ≤ B →
            ∀ (u : Vector (n+1)) (_hu : OnSphere u),
              (∫ J, sourceCapHitProbability μ Q hQ hnp (2*a)
                (fun _ => 1) contDiff_const β
                (exponentialGridHorizon γ (n+1)) (J,(u,(e,k)))
                ∂disorderLaw (n+1) μ.maxDegree) ≤
              C*(((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)+
                ((n+1 : ℕ) : ℝ)^(3-(μ.minDegree : ℝ)))+
                Real.exp (-c*((n+1 : ℕ) : ℝ)) := by
  obtain ⟨aStar,hStar,hScales⟩ :=
    actual_mixedPosterior_fixed_axis_cap_hit_source_rate_all_small_scales
      μ hd hQ hQ1 hnp hB hβ
  refine ⟨aStar,hStar,?_⟩
  intro a ha hab
  obtain ⟨T,hT,γ,c,C,hγ,hc,hC,hEvent⟩ := hScales ha hab
  refine ⟨γ,c,C,hγ,hc,hC,?_⟩
  filter_upwards [hEvent] with n hn
  intro e k he hk u hu
  have heq := sourceUncutCapHit_integral_eq_mixedPosterior_path_event
    n μ hQ hnp u hu e k a β
    (exponentialGridHorizon γ (n+1))
    (exponentialGridHorizon γ (n+1)+2*T) (le_add_right le_rfl)
  rw [heq]
  exact hn e k he hk u hu

end SlowEquilibration.ConditionedEntrance
