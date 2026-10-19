-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalWeightedReplicaMeasurability
public import SlowEquilibration.VaryingProbability

@[expose] public section

/-! # Probability reduction for the actual stronger plateau norm

The integrated squared fluctuation of the literal source observable
controls convergence of its genuine weighted-replica moment. The norm
fluctuation convergence is a primitive stochastic obligation here, not a
claimed pressure or contiguity result.
-/
namespace SlowEquilibration.SphericalWeightedReplicaPlateau
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalBarycenter VaryingProbability
open scoped Topology
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem sourceNormFluctuation_nonneg {N : ℕ} (μ : FiniteMixture)
    (β J δ q₁ q₂ q : ℝ) (D : Disorder N μ.maxDegree) :
    0 ≤ sourceNormFluctuation μ β J δ q₁ q₂ q D :=
  integral_nonneg (fun _ => sq_nonneg _)

/-- Source prop:pl-norm's integrated squared fluctuation limit implies
the actual weighted-replica moment limit on the original varying Gaussian
disorder spaces. Only eventually positive dimensions are used. -/
theorem sourceWeightedReplicaMoment_inProbability_of_fluctuation
    (μ : FiniteMixture) (β J δ q₁ q₂ q : ℝ)
    (hFluctuation : InProbability (fun N => disorderLaw N μ.maxDegree)
      (fun N => sourceNormFluctuation (N := N) μ β J δ q₁ q₂ q) 0) :
    InProbability (fun N => disorderLaw N μ.maxDegree)
      (fun N D => sourceWeightedReplicaMoment (N := N) μ β D J δ q₁ q₂) q := by
  intro ε hε
  have hLimit := hFluctuation (ε^2) (sq_pos_of_pos hε)
  refine squeeze_zero' (.of_forall fun _ => measureReal_nonneg) ?_ hLimit
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  apply measureReal_mono (μ := disorderLaw N μ.maxDegree) (h₂ := measure_ne_top _ _)
  intro D hD
  change ε^2 ≤ ‖sourceNormFluctuation μ β J δ q₁ q₂ q D-0‖
  rw [sub_zero,Real.norm_eq_abs,
    abs_of_nonneg (sourceNormFluctuation_nonneg μ β J δ q₁ q₂ q D)]
  have hAbs : ε ≤ |sourceWeightedReplicaMoment μ β D J δ q₁ q₂-q| := by
    change ε ≤ ‖sourceWeightedReplicaMoment μ β D J δ q₁ q₂-q‖ at hD
    rwa [Real.norm_eq_abs] at hD
  have hSq := pow_le_pow_left₀ hε.le hAbs 2
  rw [sq_abs] at hSq
  exact hSq.trans (sourceWeightedReplicaMoment_deviation_sq_le hN μ β J δ q₁ q₂ q D)

end
end SlowEquilibration.SphericalWeightedReplicaPlateau
