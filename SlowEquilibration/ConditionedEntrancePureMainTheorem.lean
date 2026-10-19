-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureUncutTrueRate
public import SlowEquilibration.ConditionedEntrancePureTruePosteriorLaw

/-! The proper-pure manuscript entrance estimate under the actual original
value and zero tangent-gradient conditional law. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalForm SphericalMarkedWindows SphericalGaussianJet
open SphericalAging HardSphereDynamics SphericalOverlapExponential
open scoped NNReal
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem source_pure_cap_hitting_bound_from_uniform_initial_law
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) (hd : 4 ≤ p)
    {Q B β : ℝ} (hQ : 0 < Q) (hB : 0 ≤ B) (hβ : 0 ≤ β) :
    let μ := FiniteMixture.pure p hp c hc
    ∃ aStar : ℝ, 0 < aStar ∧
      ∀ {a : ℝ}, 0 < a → a ≤ aStar →
        ∃ (γ decay C : ℝ), 0 < γ ∧ 0 < decay ∧ 0 < C ∧
          ∀ᶠ n : ℕ in atTop,
            ∀ (u : Vector (n+1)) (hu : OnSphere u) (e : ℝ), |e| ≤ B →
              (∫ J, originalTrueCapHitProbability μ β
                (exponentialGridHorizon γ (n+1)) a u J
                ∂valueConditionedLaw
                  (centerCoefficients (mixtureCoefficients μ) Q)
                  u ((onSphere_iff_norm_sq u).mp hu) e) ≤
              C*(((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)+
                ((n+1 : ℕ) : ℝ)^(3-(μ.minDegree : ℝ)))+
                Real.exp (-decay*((n+1 : ℕ) : ℝ)) := by
  dsimp only
  obtain ⟨aStar,hStar,hScales⟩ :=
    pureSourceUncut_fixed_axis_cap_hit_source_rate_all_small_scales
      p hd c hc hQ hB hβ
  refine ⟨aStar,hStar,?_⟩
  intro a ha haBound
  obtain ⟨γ,decay,C,hγ,hdecay,hC,hRate⟩ := hScales ha haBound
  refine ⟨γ,decay,C,hγ,hdecay,hC,?_⟩
  filter_upwards [hRate] with n hn
  intro u hu e he
  have hPalm := originalTrueCapHitProbability_pureValuePalm_integral_eq_source_one
    n p hp c hc hQ u ((onSphere_iff_norm_sq u).mp hu)
    e (2*a) β (exponentialGridHorizon γ (n+1))
  have hhalf : (2*a)/2 = a := by ring
  rw [hhalf] at hPalm
  rw [hPalm]
  exact hn e he u hu

end SlowEquilibration.ConditionedEntrance
