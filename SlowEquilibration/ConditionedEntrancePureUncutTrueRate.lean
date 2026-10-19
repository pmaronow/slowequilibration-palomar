-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureTrueRateBridge

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

theorem pureSourceUncut_fixed_axis_cap_hit_source_rate_all_small_scales
    (d : ℕ) (hd : 4 ≤ d) (c : ℝ) (hc : 0 < c)
    {Q B β : ℝ} (hQ : 0 < Q) (hB : 0 ≤ B) (hβ : 0 ≤ β) :
    ∃ aStar : ℝ, 0 < aStar ∧
      ∀ {a : ℝ} (_ha : 0 < a), a ≤ aStar →
        ∃ (γ decay C : ℝ), 0 < γ ∧ 0 < decay ∧ 0 < C ∧
          ∀ᶠ n : ℕ in atTop,
            ∀ (e : ℝ), |e| ≤ B →
            ∀ (u : Vector (n+1)) (_hu : OnSphere u),
              (∫ J, pureSourceCapHitProbability d (by omega) c hc Q (2*a)
                (fun _ => 1) contDiff_const β
                (exponentialGridHorizon γ (n+1)) (J,(u,(e,0)))
                ∂disorderLaw (n+1) (FiniteMixture.pure d (by omega : 2 ≤ d) c hc).maxDegree) ≤
              C*(((n+1 : ℕ) : ℝ)^(1-((FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree : ℝ)/2)+
                ((n+1 : ℕ) : ℝ)^(3-((FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree : ℝ)))+
                Real.exp (-decay*((n+1 : ℕ) : ℝ)) := by
  obtain ⟨aStar,hStar,hScales⟩ :=
    actual_pureValuePosterior_fixed_axis_cap_hit_source_rate_all_small_scales
      d hd c hc hQ hB hβ
  refine ⟨aStar,hStar,?_⟩
  intro a ha hab
  obtain ⟨T,hT,γ,decay,C,hγ,hdecay,hC,hEvent⟩ := hScales ha hab
  refine ⟨γ,decay,C,hγ,hdecay,hC,?_⟩
  filter_upwards [hEvent] with n hn
  intro e he u hu
  have heq := pureSourceUncutCapHit_integral_eq_valuePosterior_path_event
    n d (by omega) c hc hQ u hu e a β
    (exponentialGridHorizon γ (n+1))
    (exponentialGridHorizon γ (n+1)+2*T) (le_add_right le_rfl)
  rw [heq]
  exact hn e he u hu

end SlowEquilibration.ConditionedEntrance
