-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalMarkedSaddleComplexity

/-! Uniform actual radial Hessian envelopes about the genuine global saddle,
with the literal source A4 clearance controlling its integration interval. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory Filter TwoAtomStationarity
open RadialQuadraticBounds
open scoped Topology
set_option maxHeartbeats 400000

theorem sourceRadialSaddle_mem_of_clearance (μ : FiniteMixture) {β Q L R e : ℝ}
    (hm : markK μ β Q ∈ Ioo L R)
    (hClear : sourceRadialClearance μ β Q (Ioo L R)/2 ≤
      Metric.infDist (sourceRadialSaddle μ Q e) (Ioo L R)ᶜ) :
    sourceRadialSaddle μ Q e ∈ Ioo L R := by
  have hu := sourceRadialClearance_pos μ hm
  by_contra hout
  have hz := Metric.infDist_le_dist_of_mem (x := sourceRadialSaddle μ Q e)
    (show sourceRadialSaddle μ Q e ∈ (Ioo L R)ᶜ from hout)
  rw [dist_self] at hz
  linarith

theorem sourceRadialSaddle_interval_inside (μ : FiniteMixture) {β Q L R e r : ℝ}
    (hClear : sourceRadialClearance μ β Q (Ioo L R)/2 ≤
      Metric.infDist (sourceRadialSaddle μ Q e) (Ioo L R)ᶜ)
    (hr : r < sourceRadialClearance μ β Q (Ioo L R)/2) :
    Icc (sourceRadialSaddle μ Q e-r) (sourceRadialSaddle μ Q e+r) ⊆ Ioo L R := by
  intro k hk
  have hd : dist (sourceRadialSaddle μ Q e) k ≤ r := by
    rw [Real.dist_eq]
    exact abs_le.mpr (by constructor <;> linarith [hk.1,hk.2])
  exact not_not.mp (Metric.notMem_of_dist_lt_infDist
    (show dist (sourceRadialSaddle μ Q e) k < Metric.infDist (sourceRadialSaddle μ Q e) (Ioo L R)ᶜ
      from hd.trans_lt (hr.trans_le hClear)))

/-- The two actual scalar Hessian inequalities yield the matching Gaussian
bounds uniformly in energy whenever the genuine saddle is in the interval. -/
theorem sourceSaddle_profile_bounds (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (e : ℝ)
    (hm : sourceRadialSaddle μ Q e ∈ Ioo L R) :
    ∀ k ∈ Ioo L R,
      sourceSaddleComplexity μ Q e-sourceBaselineLowerCurvature μ Q L/2*(k-sourceRadialSaddle μ Q e)^2 ≤
        sourceRadialProfile μ Q e k ∧
      sourceRadialProfile μ Q e k ≤
        sourceSaddleComplexity μ Q e-sourceRadialCurvature μ Q/2*(k-sourceRadialSaddle μ Q e)^2 := by
  let f := sourceRadialProfile μ Q e
  let g := sourceRadialProfileDerivative μ Q e
  have hf (k : ℝ) (hk : k ∈ Ioo L R) : HasDerivAt f (g k) k :=
    sourceRadialProfile_hasDerivAt μ h.overlap_range.1 e k (hL.trans hk.1)
  have hg (k : ℝ) (hk : k ∈ Ioo L R) : HasDerivAt g (deriv g k) k :=
    (sourceRadialProfileDerivative_hasDerivAt μ h.overlap_range.1 e k (hL.trans hk.1)).differentiableAt.hasDerivAt
  have hs : g (sourceRadialSaddle μ Q e)=0 :=
    sourceRadialSaddle_stationary_of_above_edge μ h hnp e (hL.trans hm.1)
  have hU (k : ℝ) (hk : k ∈ Ioo L R) : deriv g k ≤ -sourceRadialCurvature μ Q :=
    sourceRadialProfile_second_derivative_le μ h.overlap_range.1 e k (hL.trans hk.1)
  have hB (k : ℝ) (hk : k ∈ Ioo L R) : -sourceBaselineLowerCurvature μ Q L ≤ deriv g k := by
    have he := sourceRadialProfile_second_derivative_ge μ h.overlap_range.1 e k (hL.trans hk.1)
    have hd : 0 < L-sourceRadialEdge μ Q := sub_pos.mpr hL
    have hp : (L-sourceRadialEdge μ Q)^2 ≤ (k-sourceRadialEdge μ Q)^2 :=
      pow_le_pow_left₀ hd.le (sub_le_sub_right hk.1.le _) 2
    have hi := one_div_le_one_div_of_le (sq_pos_of_pos hd) hp
    change -sourceRadialCurvature μ Q-1/(k-sourceRadialEdge μ Q)^2 ≤ deriv g k at he
    unfold sourceBaselineLowerCurvature
    linarith
  intro k hk
  exact ⟨quadratic_lower_of_second_derivative (convex_Ioo L R) hf hg hm hs hB k hk,
    quadratic_upper_of_second_derivative (convex_Ioo L R) hf hg hm hs hU k hk⟩
end SlowEquilibration.SphericalMarkedWindows
