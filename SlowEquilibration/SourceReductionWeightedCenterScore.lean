-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceReductionFixedCenterWeight
public import SlowEquilibration.SourceReductionTrueCapPathWeight

/-! The literal extended-valued critical-center score of manuscript
`lem:red-unions` (c), with infinite fibers assigned `⊤`. -/

@[expose] public section
namespace SlowEquilibration.SourceReductionWeightedCenterScore
noncomputable section
open Set MeasureTheory SphericalModel SphericalRotationCovariance
open SourceReductionClosedBandGraph SourceReductionFinitePathUnionBound
open SourceReductionFixedCenterWeight SourceReductionTrueCapPathWeight
open ConditionedEntrance
open SphericalAging.HardSphereDynamics
open scoped NNReal ENNReal RealInnerProductSpace
set_option autoImplicit false
set_option linter.style.haveILetI false

variable {N : ℕ}

/-- The actual sum of true-field cap-hit probabilities over the literal
window critical centers. It is `⊤` whenever the fiber is infinite. -/
def actualWindowCenterWeightedHitSum (μ : FiniteMixture)
    (Q m M a β : ℝ) (U : Set ℝ) (T : ℝ≥0)
    (J : Disorder N μ.maxDegree) : ℝ≥0∞ := by
  classical
  exact if hfinite : (windowCenters μ Q m M U J).Finite then
    ∑ u ∈ (physicalWindowCenters_finite μ Q m M U J hfinite).toFinset,
      ENNReal.ofReal (originalTrueCapHitProbability μ β T a u.1 J)
  else ⊤

theorem actualWindowCenterWeightedHitSum_of_finite (μ : FiniteMixture)
    (Q m M a β : ℝ) (U : Set ℝ) (T : ℝ≥0)
    (J : Disorder N μ.maxDegree)
    (hfinite : (windowCenters μ Q m M U J).Finite) :
    actualWindowCenterWeightedHitSum μ Q m M a β U T J =
      ∑ u ∈ (physicalWindowCenters_finite μ Q m M U J hfinite).toFinset,
        ENNReal.ofReal (originalTrueCapHitProbability μ β T a u.1 J) := by
  classical
  simp [actualWindowCenterWeightedHitSum, hfinite]

theorem actualWindowCenterWeightedHitSum_of_infinite (μ : FiniteMixture)
    (Q m M a β : ℝ) (U : Set ℝ) (T : ℝ≥0)
    (J : Disorder N μ.maxDegree)
    (hinfinite : (windowCenters μ Q m M U J).Infinite) :
    actualWindowCenterWeightedHitSum μ Q m M a β U T J = ⊤ := by
  classical
  have hnot : ¬ (windowCenters μ Q m M U J).Finite := hinfinite
  simp only [actualWindowCenterWeightedHitSum, dite_eq_right hnot]

theorem originalTrueCapHitProbability_joint_measurable (hN : 2 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0) (a : ℝ) :
    Measurable (fun z : Disorder N μ.maxDegree × PhysicalSphere N =>
      ENNReal.ofReal (originalTrueCapHitProbability μ β T a z.2.1 z.1)) := by
  have heq (z : Disorder N μ.maxDegree × PhysicalSphere N) :
      originalTrueCapHitProbability μ β T a z.2.1 z.1 =
        actualFixedCenterPathHitProbability hN μ β T a z.1 z.2 := by
    rw [actualFixedCenterPathHitProbability_eq,
      uniformRealPathKernel_original_true_cap_probability]
  simp_rw [heq]
  exact ENNReal.measurable_ofReal.comp
    (actualFixedCenterPathHitProbability_measurable hN μ β T a)

end
end SlowEquilibration.SourceReductionWeightedCenterScore
