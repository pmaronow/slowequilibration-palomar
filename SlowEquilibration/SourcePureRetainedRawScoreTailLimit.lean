-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureRetainedRawScoreTail

/-! Every selected pure value upper-tail mean limit is the same limit
for the literal original energy/radial-score upper-tail count. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter MeasureTheory SphericalModel SphericalGaussianJet
open SlowEquilibration.PairConditionalDeterminantMoments
open scoped ENNReal Topology
set_option autoImplicit false

theorem sourcePureRetainedRawScoreUpperTail_mean_tendsto
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    (Q E δ : ℝ) (m : ℕ → ℝ) (t κ C ε η G b : ℝ)
    (hret : Tendsto (fun n : ℕ =>
      sourceRetainedValueWindowMean (n+2) (FiniteMixture.pure p hp a ha) Q
        (sourcePureCenteredUpperTailNormalizedWindow n m E δ t)
        κ C ε η E G) atTop (𝓝 b)) :
    Tendsto (fun n : ℕ =>
      (∫⁻ J, sourceRetainedScoreWindowCount (n+2)
        (centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp a ha)) Q)
        {z : EuclideanSpace ℝ (Fin 2) |
          z 0 ∈ sourcePureCenteredRawUpperTailNormalizedWindow n m t ∧
          z 1 ∈ Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))}
        κ C ε η E G J
        ∂disorderLaw (n+3) (FiniteMixture.pure p hp a ha).maxDegree).toReal)
      atTop (𝓝 b) := by
  apply hret.congr'
  exact Filter.Eventually.of_forall fun n =>
    (sourcePureRetainedRawScoreUpperTail_mean_eq_clippedValueWindow
      n p hp a ha Q E δ m t κ C ε η G).symm

end SlowEquilibration.SphericalMarkedWindows
