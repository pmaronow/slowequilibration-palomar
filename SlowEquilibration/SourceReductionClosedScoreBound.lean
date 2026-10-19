-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceReductionWeightedCenterScore
public import SlowEquilibration.SourceReductionEvolvedCapMass

/-! Both inequalities of the manuscript critical-cap path union bound hold
for every original tensor-disorder realization. The center score is assigned
infinite value when the center fiber is infinite. -/

@[expose] public section
namespace SlowEquilibration.SourceReductionClosedScoreBound
noncomputable section
open Set MeasureTheory ProbabilityTheory SphericalModel SphericalDynamics
open SourceReductionWeightedCenterScore SourceReductionEvolvedCapMass
open SourceReductionClosedBandGraph SourceReductionClosedPathUnionGraph
open SourceReductionFinitePathUnionBound SourceReductionTrueCapPathWeight
open SphericalKacRiceHittingSource SphericalRealTimePathKernel
open SphericalRotationCovariance SphericalFieldKernels
open ConditionedEntrance
open SphericalAging.HardSphereDynamics
open scoped NNReal ENNReal RealInnerProductSpace Topology
set_option autoImplicit false
set_option maxHeartbeats 800000

variable {N : ℕ}

/-- The actual original-diffusion path-hit probability is bounded by the
literal sum of the true-field one-center marks for every disorder. -/
theorem actualWindowPathHitProbability_le_weightedScore (hN : 2 ≤ N)
    (μ : FiniteMixture) (Q m M a β : ℝ) (U : Set ℝ)
    (T : ℝ≥0) (J : Disorder N μ.maxDegree) :
    ENNReal.ofReal (actualWindowPathHitProbability hN μ Q m M a β U T J) ≤
      actualWindowCenterWeightedHitSum μ Q m M a β U T J := by
  classical
  by_cases hfinite : (windowCenters μ Q m M U J).Finite
  · let hs := physicalWindowCenters_finite μ Q m M U J hfinite
    have hunion := actualWindowPathHitProbability_le_sum
      hN μ Q m M a β U T J hfinite
    calc
      ENNReal.ofReal (actualWindowPathHitProbability hN μ Q m M a β U T J) ≤
          ENNReal.ofReal
            (∑ u ∈ hs.toFinset,
              (uniformRealPathKernel hN μ β T (fieldMap μ J)).real
                {p | (p,u) ∈ overlapSupEvent T a}) :=
        ENNReal.ofReal_le_ofReal hunion
      _ = ∑ u ∈ hs.toFinset,
            ENNReal.ofReal ((uniformRealPathKernel hN μ β T (fieldMap μ J)).real
              {p | (p,u) ∈ overlapSupEvent T a}) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro u hu
        exact measureReal_nonneg
      _ = ∑ u ∈ hs.toFinset,
            ENNReal.ofReal (originalTrueCapHitProbability μ β T a u.1 J) := by
        apply Finset.sum_congr rfl
        intro u hu
        exact congrArg ENNReal.ofReal
          (uniformRealPathKernel_original_true_cap_probability hN μ β T a J u)
      _ = actualWindowCenterWeightedHitSum μ Q m M a β U T J :=
        (actualWindowCenterWeightedHitSum_of_finite μ Q m M a β U T J hfinite).symm
  · have hinfinite : (windowCenters μ Q m M U J).Infinite := hfinite
    rw [actualWindowCenterWeightedHitSum_of_infinite μ Q m M a β U T J hinfinite]
    exact le_top

/-- The two literal inequalities of `lem:red-unions` (c), with the
semigroup time supremum, actual continuous-path event, and actual
true-posterior critical-center score. -/
theorem evolved_pointCap_sup_le_weightedScore (hN : 2 ≤ N)
    (μ : FiniteMixture) (Q m M a β : ℝ)
    {U : Set ℝ} (hU : IsClosed U) (T : ℝ≥0)
    (J : Disorder N μ.maxDegree) :
    ENNReal.ofReal (sSup {r : ℝ | ∃ t : RealPathTime T,
      r = (mixedTransitionKernel μ J β (SourceReductionPathMarginal.nnrealTime t)
        ∘ₘ sphereLaw N).real
          (ambientPointCapUnion μ Q m M a U J)}) ≤
      actualWindowCenterWeightedHitSum μ Q m M a β U T J := by
  exact (ENNReal.ofReal_le_ofReal
    (evolved_pointCap_sup_le_pathHit hN μ Q m M a β hU T J)).trans
      (actualWindowPathHitProbability_le_weightedScore hN μ Q m M a β U T J)

end
end SlowEquilibration.SourceReductionClosedScoreBound
