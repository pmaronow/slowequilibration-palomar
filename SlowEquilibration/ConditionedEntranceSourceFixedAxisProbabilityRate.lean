-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceRateAllSmallScales
public import SlowEquilibration.ConditionedEntranceSourceFixedAxisRotation
public import SlowEquilibration.ConditionedEntranceActualCutoff

/-! Source-rate bound for the original-disorder probability observable at
every prescribed physical axis and every sufficiently small cap scale. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalForm SphericalOverlapExponential
open SphericalAging HardSphereDynamics
open scoped NNReal
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem actual_mixedSource_fixed_axis_probability_rate_all_small_scales
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
                sourceScalarCutoff sourceScalarCutoff_contDiff_two β
                (exponentialGridHorizon γ (n+1)) (J,(u,(e,k)))
                ∂disorderLaw (n+1) μ.maxDegree) ≤
              C*(((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)+
                ((n+1 : ℕ) : ℝ)^(3-(μ.minDegree : ℝ)))+
                Real.exp (-c*((n+1 : ℕ) : ℝ)) := by
  obtain ⟨aStar,hStar,hScales⟩ :=
    actual_mixedSource_axis_averaged_cap_hit_source_rate_all_small_scales
      μ hd hQ hQ1 hnp hB hβ sourceScalarCutoff
      sourceScalarCutoff_contDiff_two sourceScalarCutoff_abs_le_one
      (fun _ hs => sourceScalarCutoff_zero_of_two_lt_abs hs)
  refine ⟨aStar,hStar,?_⟩
  intro a ha hab
  obtain ⟨γ,c,C,hγ,hc,hC,hEvent⟩ := hScales ha hab
  refine ⟨γ,c,C,hγ,hc,hC,?_⟩
  filter_upwards [hEvent] with n hn
  intro e k he hk u hu
  rw [sourceCapHitProbability_annealed_fixed_axis_eq_average
    (by omega : 1 ≤ n+1) μ hnp Q hQ hQ1 (2*a)
    (mul_pos (by norm_num) ha) sourceScalarCutoff
    sourceScalarCutoff_contDiff_two e k β
    (exponentialGridHorizon γ (n+1)) u hu]
  exact hn e k he hk

end SlowEquilibration.ConditionedEntrance
