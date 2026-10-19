-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalConvexRSLower
public import SlowEquilibration.SphericalExponentialTransfer

/-! Actual replica-symmetric concentration and planted-to-Gibbs-reference
transfer for globally convex finite covariances. The physical thermodynamic limit is supplied by
the proved HS lower bound, not by a pressure-limit assumption. -/

@[expose] public section
namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

theorem convex_annealed_logPartition_concentration (μ : FiniteMixture)
    (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi) {β ε : ℝ}
    (hβ : 0 < β) (hβs : β ≤ Thresholds.staticThreshold μ.xi) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (disorderLaw N μ.maxDegree).real
        {J | |Real.log (mixturePartition μ β J)/(N : ℝ)-β^2*μ.xi 1/2| > ε} ≤
          2*Real.exp (-(ε^2*(N : ℝ))/(8*β^2*μ.xi 1)) :=
  annealed_logPartition_concentration_eventually_of_pressure_limit μ hβ
    (convex_quenchedPressure_tendsto_annealed_le_static μ hconv hβ.le hβs) hε

theorem convex_exponential_planted_transfer (μ : FiniteMixture)
    (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi) {β c : ℝ}
    (hβ : 0 < β) (hβs : β ≤ Thresholds.staticThreshold μ.xi) (hc : 0 < c)
    (E : (N : ℕ) → Set (Disorder N μ.maxDegree × Vector N))
    (hE : ∀ N, MeasurableSet (E N))
    (hP : ∀ᶠ N : ℕ in atTop,
      (plantedLaw (mixtureCoefficients μ) β).real (E N) ≤ Real.exp (-c*(N : ℝ))) :
    ∀ᶠ N : ℕ in atTop,
      (gibbsReferenceLaw (mixtureCoefficients μ) β).real (E N) ≤
        3*Real.exp (-plantedTransferRate μ β c*(N : ℝ)) :=
  exponential_planted_transfer_eventually_of_pressure_limit μ hβ hc
    (convex_quenchedPressure_tendsto_annealed_le_static μ hconv hβ.le hβs) E hE hP

end
end SlowEquilibration.SphericalModel
