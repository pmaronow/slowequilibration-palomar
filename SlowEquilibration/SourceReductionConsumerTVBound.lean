-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceReductionConsumerBandBound
public import SlowEquilibration.Separation

/-! The literal fixed-time total-variation test of source
`prop:red-consumer` against the original Gibbs law. -/

@[expose] public section
namespace SlowEquilibration.SourceReductionConsumerTVBound
noncomputable section
open Set MeasureTheory ProbabilityTheory SphericalModel SphericalDynamics
open SourceReductionClosedBandGraph SourceReductionConsumerBandBound
open SourceReductionWeightedCenterScore SourceReductionPathMarginal
open SphericalRealTimePathKernel SphericalAging.HardSphereDynamics
open scoped NNReal ENNReal RealInnerProductSpace Topology
set_option autoImplicit false
set_option maxHeartbeats 850000
set_option linter.style.haveILetI false

variable {N : ℕ}

theorem actualWindowCenterWeightedHitSum_ne_top_of_finite
    (μ : FiniteMixture) (Q m M a β : ℝ) (U : Set ℝ)
    (T : ℝ≥0) (J : Disorder N μ.maxDegree)
    (hfinite : (windowCenters μ Q m M U J).Finite) :
    actualWindowCenterWeightedHitSum μ Q m M a β U T J ≠ ⊤ := by
  rw [actualWindowCenterWeightedHitSum_of_finite μ Q m M a β U T J hfinite]
  exact (ENNReal.sum_lt_top.mpr (fun u hu => by
    exact ENNReal.ofReal_lt_top)).ne

/-- For every finite original critical-center fiber, the actual
uniform-start diffusion remains separated from the literal original Gibbs
law by the Gibbs mass outside the band union and the true cap-hit score. -/
theorem original_consumer_tv_lower_of_finite (hN : 2 ≤ N)
    (μ : FiniteMixture) (Q m M b a β : ℝ)
    {U : Set ℝ} (hU : IsClosed U) (T : ℝ≥0)
    (J : Disorder N μ.maxDegree) (t : RealPathTime T)
    (ha : a < Real.sqrt Q - b)
    (hfinite : (windowCenters μ Q m M U J).Finite) :
    1 - (mixtureGibbsLaw μ β J).real
        (ambientWindowBandUnion μ Q m M b U J)ᶜ -
      (actualWindowCenterWeightedHitSum μ Q m M a β U T J).toReal ≤
      totalVariation
        (mixedTransitionKernel μ J β (nnrealTime t) ∘ₘ sphereLaw N)
        (mixtureGibbsLaw μ β J) := by
  let ρ := mixedTransitionKernel μ J β (nnrealTime t) ∘ₘ sphereLaw N
  let π := mixtureGibbsLaw μ β J
  let B := ambientWindowBandUnion μ Q m M b U J
  letI : IsProbabilityMeasure (sphereLaw N) := sphereLaw_probability N
  letI : IsProbabilityMeasure ρ := inferInstance
  letI : IsProbabilityMeasure π := mixtureGibbsLaw_probability (by omega : 1 ≤ N) μ β J
  have hB : MeasurableSet B :=
    (ambientWindowBandUnion_isClosed μ Q m M b hU J).measurableSet
  have hscoreTop : actualWindowCenterWeightedHitSum μ Q m M a β U T J ≠ ⊤ :=
    actualWindowCenterWeightedHitSum_ne_top_of_finite μ Q m M a β U T J hfinite
  have hbandENN : ENNReal.ofReal (ρ.real B) ≤
      actualWindowCenterWeightedHitSum μ Q m M a β U T J :=
    evolved_band_le_weightedScore hN μ Q m M b a β hU T J t ha
  have hband : ρ.real B ≤
      (actualWindowCenterWeightedHitSum μ Q m M a β U T J).toReal := by
    have hh := ENNReal.toReal_mono hscoreTop hbandENN
    simpa only [ENNReal.toReal_ofReal measureReal_nonneg] using hh
  have hsep := separation_from_event ρ π hB
  dsimp only [ρ,π,B] at *
  linarith

/-- The manuscript's all-disorder inequality, with the infinite-score case
encoded explicitly rather than subtracting `+∞` in the real numbers. -/
theorem original_consumer_tv_lower (hN : 2 ≤ N)
    (μ : FiniteMixture) (Q m M b a β : ℝ)
    {U : Set ℝ} (hU : IsClosed U) (T : ℝ≥0)
    (J : Disorder N μ.maxDegree) (t : RealPathTime T)
    (ha : a < Real.sqrt Q - b) :
    actualWindowCenterWeightedHitSum μ Q m M a β U T J = ⊤ ∨
      1 - (mixtureGibbsLaw μ β J).real
          (ambientWindowBandUnion μ Q m M b U J)ᶜ -
        (actualWindowCenterWeightedHitSum μ Q m M a β U T J).toReal ≤
        totalVariation
          (mixedTransitionKernel μ J β (nnrealTime t) ∘ₘ sphereLaw N)
          (mixtureGibbsLaw μ β J) := by
  by_cases hfinite : (windowCenters μ Q m M U J).Finite
  · exact Or.inr (original_consumer_tv_lower_of_finite hN μ Q m M b a β
      hU T J t ha hfinite)
  · exact Or.inl (actualWindowCenterWeightedHitSum_of_infinite μ Q m M a β U T J hfinite)

end
end SlowEquilibration.SourceReductionConsumerTVBound
