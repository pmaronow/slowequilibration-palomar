-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureRateAllSmallScales
public import SlowEquilibration.SourceConditionedCPTransferPureAxisAverage
public import SlowEquilibration.ConditionedEntranceActualCutoff

/-! Source-rate bound for the original-disorder probability observable at
every prescribed physical axis and every sufficiently small cap scale. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalForm SphericalOverlapExponential
open SphericalAging HardSphereDynamics
open SourceConditionedCPTransferPureAxisAverage
open scoped NNReal
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem actual_pureSource_fixed_axis_probability_rate_all_small_scales
    (d : ℕ) (hd : 4 ≤ d) (c : ℝ) (hc : 0 < c)
    {Q B β : ℝ} (hQ : 0 < Q) (hB : 0 ≤ B) (hβ : 0 ≤ β) :
    ∃ aStar : ℝ, 0 < aStar ∧
      ∀ {a : ℝ} (_ha : 0 < a), a ≤ aStar →
        ∃ (γ decay C : ℝ), 0 < γ ∧ 0 < decay ∧ 0 < C ∧
          ∀ᶠ n : ℕ in atTop,
            ∀ (e : ℝ), |e| ≤ B →
            ∀ (u : Vector (n+1)) (_hu : OnSphere u),
              (∫ J, pureSourceCapHitProbability d (by omega) c hc Q (2*a)
                sourceScalarCutoff sourceScalarCutoff_contDiff_two β
                (exponentialGridHorizon γ (n+1)) (J,(u,(e,0)))
                ∂disorderLaw (n+1) (FiniteMixture.pure d (by omega : 2 ≤ d) c hc).maxDegree) ≤
              C*(((n+1 : ℕ) : ℝ)^(1-((FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree : ℝ)/2)+
                ((n+1 : ℕ) : ℝ)^(3-((FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree : ℝ)))+
                Real.exp (-decay*((n+1 : ℕ) : ℝ)) := by
  obtain ⟨aStar,hStar,hScales⟩ :=
    actual_pureSource_axis_averaged_cap_hit_source_rate_all_small_scales
      d hd c hc hQ hB hβ sourceScalarCutoff
      sourceScalarCutoff_contDiff_two sourceScalarCutoff_abs_le_one
      (fun _ hs => sourceScalarCutoff_zero_of_two_lt_abs hs)
  refine ⟨aStar,hStar,?_⟩
  intro a ha hab
  obtain ⟨γ,decay,C,hγ,hdecay,hC,hEvent⟩ := hScales ha hab
  refine ⟨γ,decay,C,hγ,hdecay,hC,?_⟩
  filter_upwards [hEvent] with n hn
  intro e he u hu
  rw [pureSourceCapHitProbability_annealed_fixed_axis_eq_average
    (by omega : 1 ≤ n+1) d (by omega) c hc Q (2*a) sourceScalarCutoff
    sourceScalarCutoff_contDiff_two e β
    (exponentialGridHorizon γ (n+1)) u hu]
  exact hn e he

end SlowEquilibration.ConditionedEntrance
