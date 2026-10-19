-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceActualLocalCoupling
public import SlowEquilibration.ConditionedEntranceSourceCutoffHitProbability
public import SlowEquilibration.SphericalPosteriorGradientPathGrid

/-! The exact true/cutoff/gradient union bound on each Gaussian disorder and
spherical starting-state fibre. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet SphericalDynamics
open SphericalPosteriorMaps SphericalMarkedWindows
open SphericalPosteriorGradientIndependence SphericalOverlapExponential
open SphericalAging HardSphereDynamics SmoothKilled
open scoped NNReal RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem actual_mixedPosterior_cap_hit_le_sourceCutoff_add_gradient
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (hnp : μ.minDegree < μ.maxDegree)
    (g : EuclideanDisorder (n+1) μ.maxDegree)
    (u : Vector (n+1)) (hu : OnSphere u)
    (e k a : ℝ) (ha : 0 < a) (β : ℝ)
    (x : Vector (n+1)) (hx : OnSphere x) (T : ℝ≥0) :
    let J := unpackDisorder g
    let Jpost := unpackDisorder
      (mixedPosterior n μ Q u (scorePairEquiv (e,k)) g)
    let G := surfaceGradient
      (field (centerCoefficients (mixtureCoefficients μ) Q) J) u
    let D := SourceData.atSourceParameters (by omega : 1 ≤ n+1)
      μ hnp Q hQ hQ1 (2*a) (mul_pos (by norm_num) ha)
      sourceScalarCutoff sourceScalarCutoff_contDiff_two (J,(u,(e,k))) hu
    (VectorBrownian.law (n+1)).real {ω | ∃ t : ℝ≥0, t ≤ T ∧
      a ≤ |overlapValue u (mixedProcess μ Jpost β x t ω)|} ≤
    (VectorBrownian.law (n+1)).real {ω | ∃ t : ℝ≥0, t ≤ T ∧
      a ≤ |overlapValue u (SmoothKilled.process D β x t ω)|} +
    (VectorBrownian.law (n+1)).real {ω | ∃ t : ℝ≥0, t ≤ T ∧
      2*a ≤ |gradientScore G (mixedProcess μ Jpost β x t ω)|} := by
  dsimp only
  let J := unpackDisorder g
  let Jpost := unpackDisorder (mixedPosterior n μ Q u (scorePairEquiv (e,k)) g)
  let G := surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u
  let D := SourceData.atSourceParameters (by omega : 1 ≤ n+1)
    μ hnp Q hQ hQ1 (2*a) (mul_pos (by norm_num) ha)
    sourceScalarCutoff sourceScalarCutoff_contDiff_two (J,(u,(e,k))) hu
  let r : ℝ≥0 → VectorBrownian.Space (n+1) → ℝ :=
    fun t ω => overlapValue u (mixedProcess μ Jpost β x t ω)
  let s : ℝ≥0 → VectorBrownian.Space (n+1) → ℝ :=
    fun t ω => gradientScore G (mixedProcess μ Jpost β x t ω)
  let rCut : ℝ≥0 → VectorBrownian.Space (n+1) → ℝ :=
    fun t ω => overlapValue u (SmoothKilled.process D β x t ω)
  have hr : ∀ᵐ ω ∂VectorBrownian.law (n+1),
      Continuous (fun t => r t ω) := by
    filter_upwards [mixedProcess_continuous μ Jpost β x] with ω hc
    exact (overlapLinear u).continuous.comp hc
  have hlocal := actual_mixedPosterior_sourceCutoff_agree_before_exit
    n μ Q hQ hQ1 hnp g u hu e k (2*a)
    (mul_pos (by norm_num) ha) β x hx T
  have hagree : ∀ᵐ ω ∂VectorBrownian.law (n+1), ∀ t : ℝ≥0,
      t ≤ T → (∀ v : ℝ≥0, v < t → |r v ω| < 2*a ∧ |s v ω| < 2*a) →
        r t ω = rCut t ω := by
    filter_upwards [hlocal] with ω hω
    intro t ht hbefore
    apply congrArg (overlapValue u)
    apply hω t ht
    intro v hv
    have hh := hbefore v hv
    have heq : overlapValue u (mixedProcess μ Jpost β x v ω) =
        overlap (mixedProcess μ Jpost β x v ω) u := by
      rw [overlapValue_eq,overlap,real_inner_comm]
    apply max_lt_iff.mpr
    constructor
    · rw [← heq,abs_div,abs_of_pos (mul_pos (by norm_num) ha)]
      exact (div_lt_iff₀ (mul_pos (by norm_num) ha)).mpr (by simpa only [one_mul] using hh.1)
    · have heq' : inner ℝ G (mixedProcess μ Jpost β x v ω) /
          (((n+1 : ℕ) : ℝ) * (2*a)) =
          gradientScore G (mixedProcess μ Jpost β x v ω) / (2*a) := by
        dsimp only [gradientScore]
        ring
      rw [heq',abs_div,abs_of_pos (mul_pos (by norm_num) ha)]
      exact (div_lt_iff₀ (mul_pos (by norm_num) ha)).mpr (by simpa only [one_mul] using hh.2)
  exact cap_hit_probability_le_cut_add_gradient (VectorBrownian.law (n+1))
    r s rCut T (by linarith : a < 2*a) hr hagree

end SlowEquilibration.ConditionedEntrance
