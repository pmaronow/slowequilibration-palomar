-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceReductionBandCapGeometry
public import SlowEquilibration.SourceReductionClosedScoreBound

/-! Deterministic band-visit half of source `prop:red-consumer`, using the
original spherical diffusion and original critical-center score. -/

@[expose] public section
namespace SlowEquilibration.SourceReductionConsumerBandBound
noncomputable section
open Set MeasureTheory ProbabilityTheory SphericalModel SphericalDynamics
open SourceReductionClosedBandGraph SourceReductionClosedScoreBound
open SourceReductionClosedPathUnionGraph
open SourceReductionBandCapGeometry SourceReductionEvolvedCapMass
open SourceReductionWeightedCenterScore SourceReductionPathMarginal
open SphericalRealTimePathKernel
open SphericalKacRiceHittingSource
open SphericalAging.HardSphereDynamics
open scoped NNReal ENNReal RealInnerProductSpace Topology
set_option autoImplicit false
set_option maxHeartbeats 800000

variable {N : ℕ}

/-- The literal ambient original-spin band union for one disorder. -/
def ambientWindowBandUnion (μ : FiniteMixture) (Q m M b : ℝ)
    (U : Set ℝ) (J : Disorder N μ.maxDegree) : Set (Vector N) :=
  {x | (J,x) ∈ physicalSphereBandUnionGraph μ Q m M b U}

theorem ambientWindowBandUnion_isClosed (μ : FiniteMixture)
    (Q m M b : ℝ) {U : Set ℝ} (hU : IsClosed U)
    (J : Disorder N μ.maxDegree) :
    IsClosed (ambientWindowBandUnion μ Q m M b U J) :=
  (physicalSphereBandUnionGraph_isClosed (N := N) μ Q m M b hU).preimage
    (continuous_const.prodMk continuous_id)

/-- At every time up to the prescribed horizon, the literal evolved
uniform-start mass of the critical-center band union is dominated by the
extended nonnegative true-field cap-hit score, for every disorder. -/
theorem evolved_band_le_weightedScore (hN : 2 ≤ N)
    (μ : FiniteMixture) (Q m M b a β : ℝ)
    {U : Set ℝ} (hU : IsClosed U) (T : ℝ≥0)
    (J : Disorder N μ.maxDegree) (t : RealPathTime T)
    (ha : a < Real.sqrt Q - b) :
    ENNReal.ofReal
      ((mixedTransitionKernel μ J β (nnrealTime t) ∘ₘ sphereLaw N).real
        (ambientWindowBandUnion μ Q m M b U J)) ≤
      actualWindowCenterWeightedHitSum μ Q m M a β U T J := by
  have hsub : ambientWindowBandUnion μ Q m M b U J ⊆
      ambientPointCapUnion μ Q m M a U J :=
    physicalSphereBandUnion_subset_pointCapUnion μ Q m M b a U J ha
  calc
    ENNReal.ofReal
        ((mixedTransitionKernel μ J β (nnrealTime t) ∘ₘ sphereLaw N).real
          (ambientWindowBandUnion μ Q m M b U J)) ≤
      ENNReal.ofReal
        ((mixedTransitionKernel μ J β (nnrealTime t) ∘ₘ sphereLaw N).real
          (ambientPointCapUnion μ Q m M a U J)) :=
      ENNReal.ofReal_le_ofReal (measureReal_mono hsub)
    _ ≤ ENNReal.ofReal
        (actualWindowPathHitProbability hN μ Q m M a β U T J) :=
      ENNReal.ofReal_le_ofReal
        (evolved_pointCap_le_pathHit hN μ Q m M a β hU T J t)
    _ ≤ _ := actualWindowPathHitProbability_le_weightedScore
      hN μ Q m M a β U T J

end
end SlowEquilibration.SourceReductionConsumerBandBound
