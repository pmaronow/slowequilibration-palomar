-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureActualLocalCoupling
public import SlowEquilibration.ConditionedEntranceSourceCutoffHitProbability

/-! The proper pure true-process cap-hit event is covered by a cutoff-process
cap hit or a center-gradient exit, on each Wiener fibre. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet SphericalDynamics
open SphericalPosteriorMaps SphericalPosteriorGradientIndependence
open SphericalOverlapExponential
open SphericalAging HardSphereDynamics
open scoped NNReal RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem actual_pureValuePosterior_cap_hit_le_sourceCutoff_add_gradient
    (n p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (Q : ℝ) (hQ : 0 < Q)
    (g : EuclideanDisorder (n+1) (FiniteMixture.pure p hp c hc).maxDegree)
    (u : Vector (n+1)) (hu : OnSphere u)
    (e a : ℝ) (ha : 0 < a) (β : ℝ)
    (x : Vector (n+1)) (hx : OnSphere x) (T : ℝ≥0) :
    let μ := FiniteMixture.pure p hp c hc
    let J := unpackDisorder g
    let Jpost := unpackDisorder (valuePosterior n μ Q u e g)
    let G := surfaceGradient
      (field (centerCoefficients (mixtureCoefficients μ) Q) J) u
    let D := SmoothKilledGeneral.FieldData.ofPure (by omega : 1 ≤ n+1)
      p hp c hc Q J u e (2*a) sourceScalarCutoff sourceScalarCutoff_contDiff_two
    (VectorBrownian.law (n+1)).real {ω | ∃ t : ℝ≥0, t ≤ T ∧
      a ≤ |overlapValue u (mixedProcess μ Jpost β x t ω)|} ≤
    (VectorBrownian.law (n+1)).real {ω | ∃ t : ℝ≥0, t ≤ T ∧
      a ≤ |overlapValue u (SmoothKilledGeneral.process D β x t ω)|} +
    (VectorBrownian.law (n+1)).real {ω | ∃ t : ℝ≥0, t ≤ T ∧
      2*a ≤ |gradientScore G (mixedProcess μ Jpost β x t ω)|} := by
  dsimp only
  let μ := FiniteMixture.pure p hp c hc
  let J := unpackDisorder g
  let Jpost := unpackDisorder (valuePosterior n μ Q u e g)
  let G := surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u
  let D := SmoothKilledGeneral.FieldData.ofPure (by omega : 1 ≤ n+1)
    p hp c hc Q J u e (2*a) sourceScalarCutoff sourceScalarCutoff_contDiff_two
  let r : ℝ≥0 → VectorBrownian.Space (n+1) → ℝ :=
    fun t ω => overlapValue u (mixedProcess μ Jpost β x t ω)
  let s : ℝ≥0 → VectorBrownian.Space (n+1) → ℝ :=
    fun t ω => gradientScore G (mixedProcess μ Jpost β x t ω)
  let rCut : ℝ≥0 → VectorBrownian.Space (n+1) → ℝ :=
    fun t ω => overlapValue u (SmoothKilledGeneral.process D β x t ω)
  have hr : ∀ᵐ ω ∂VectorBrownian.law (n+1),
      Continuous (fun t => r t ω) := by
    filter_upwards [mixedProcess_continuous μ Jpost β x] with ω hc'
    exact (overlapLinear u).continuous.comp hc'
  have hlocal := actual_pureValuePosterior_sourceCutoff_agree_before_exit
    n p hp c hc Q hQ g u hu e (2*a) β x hx T
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
      exact (div_lt_iff₀ (mul_pos (by norm_num) ha)).mpr
        (by simpa only [one_mul] using hh.1)
    · have heq' : inner ℝ G (mixedProcess μ Jpost β x v ω) /
          (((n+1 : ℕ) : ℝ) * (2*a)) =
          gradientScore G (mixedProcess μ Jpost β x v ω) / (2*a) := by
        dsimp only [gradientScore]
        ring
      rw [heq',abs_div,abs_of_pos (mul_pos (by norm_num) ha)]
      exact (div_lt_iff₀ (mul_pos (by norm_num) ha)).mpr
        (by simpa only [one_mul] using hh.2)
  exact cap_hit_probability_le_cut_add_gradient (VectorBrownian.law (n+1))
    r s rCut T (by linarith : a < 2*a) hr hagree

end SlowEquilibration.ConditionedEntrance
