-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianSpinInterpolation

@[expose] public section

namespace SlowEquilibration.GaussianSpinInterpolation

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace V]

theorem score_eq_sum_projections (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (w : EuclideanSpace ℝ ι) :
    score ν L w = ∑ i,
      expectation ν (fun v => L v (EuclideanSpace.single i 1)) L w • PiLp.proj 2 (fun _ : ι => ℝ) i := by
  ext d
  rw [score_eq_coordinate_sum ν L hL hb]
  simp only [sum_apply, smul_apply, PiLp.proj_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- The derivative of the literal sphere-integral logarithm is itself C¹.
The finite coordinate sum represents a derivative on disorder space, while
the spin measure remains arbitrary and may be nonatomic. -/
theorem score_contDiff (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) : ContDiff ℝ 1 (score ν L) := by
  have heq : score ν L = fun w => ∑ i,
      expectation ν (fun v => L v (EuclideanSpace.single i 1)) L w • PiLp.proj 2 (fun _ : ι => ℝ) i :=
    funext (score_eq_sum_projections ν L hL hb)
  rw [heq]
  apply ContDiff.sum
  intro i _
  have hρ : Measurable (fun v => L v (EuclideanSpace.single i 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).continuous.measurable.comp hL
  have hρb : ∀ᵐ v ∂ν, |L v (EuclideanSpace.single i 1)| ≤ K ∧ ‖L v‖ ≤ K := by
    filter_upwards [hb] with v hv
    have hh := (L v).le_opNorm (EuclideanSpace.single i 1)
    have he : ‖(EuclideanSpace.single i 1 : EuclideanSpace ℝ ι)‖ = 1 := by simp
    rw [Real.norm_eq_abs, he, mul_one] at hh
    exact ⟨hh.trans hv, hv⟩
  exact (expectation_contDiff ν _ L hρ hL hK hK hρb).smul contDiff_const

theorem logPartition_contDiff_two (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) : ContDiff ℝ 2 (logPartition ν L) :=
  contDiff_succ_iff_hasFDerivAt.mpr ⟨score ν L, score_contDiff ν L hL hK hb,
    logPartition_hasFDerivAt ν L hL hK hb⟩

/-- The ordinary Hessian of the integral log partition. -/
def hessian (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (w : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι →L[ℝ] (EuclideanSpace ℝ ι →L[ℝ] ℝ) := fderiv ℝ (score ν L) w

theorem score_hasFDerivAt (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (w : EuclideanSpace ℝ ι) :
    HasFDerivAt (score ν L) (hessian ν L w) w :=
  (score_contDiff ν L hL hK hb).differentiable (by norm_num) w |>.hasFDerivAt

omit [DecidableEq ι] in
theorem directionalObservable_bound (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    {K : ℝ} (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (d : EuclideanSpace ℝ ι) :
    ∀ᵐ v ∂ν, |L v d| ≤ K*‖d‖ ∧ ‖L v‖ ≤ K := by
  filter_upwards [hb] with v hv
  have hh := (L v).le_opNorm d
  rw [Real.norm_eq_abs] at hh
  exact ⟨hh.trans (mul_le_mul_of_nonneg_right hv (norm_nonneg _)), hv⟩

theorem hessian_apply_eq_expectationDerivative (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (w d e : EuclideanSpace ℝ ι) :
    hessian ν L w d e = expectationDerivative ν (fun v => L v e) L w d := by
  have hρ : Measurable (fun v => L v e) :=
    (ContinuousLinearMap.apply ℝ ℝ e).continuous.measurable.comp hL
  have hExp := expectation_hasFDerivAt ν _ L hρ hL (mul_nonneg hK (norm_nonneg _)) hK
    (directionalObservable_bound ν L hb e) w
  have hScore := (ContinuousLinearMap.apply ℝ ℝ e).hasFDerivAt.comp w (score_hasFDerivAt ν L hL hK hb w)
  have heq : (fun y => score ν L y e) = expectation ν (fun v => L v e) L :=
    funext (fun y => score_apply ν L hL hb y e)
  change HasFDerivAt (fun y => score ν L y e)
    ((ContinuousLinearMap.apply ℝ ℝ e).comp (hessian ν L w)) w at hScore
  rw [heq] at hScore
  have h := congrArg (fun l : EuclideanSpace ℝ ι →L[ℝ] ℝ => l d) (hScore.unique hExp)
  exact h

/-- The literal Hessian is the ordinary Gibbs covariance of two directional
field observables. -/
theorem hessian_apply_covariance (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (w d e : EuclideanSpace ℝ ι) :
    hessian ν L w d e = expectation ν (fun v => L v e * L v d) L w -
      expectation ν (fun v => L v e) L w * expectation ν (fun v => L v d) L w := by
  rw [hessian_apply_eq_expectationDerivative ν L hL hK hb]
  exact expectationDerivative_apply ν _ L
    ((ContinuousLinearMap.apply ℝ ℝ e).continuous.measurable.comp hL) hL
    (directionalObservable_bound ν L hb e) w d

/-- The dimension-free Hessian bound needed for actual Gaussian-step
recursions. It is derived from the bounded physical spin features. -/
theorem norm_hessian_le (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (w : EuclideanSpace ℝ ι) :
    ‖hessian ν L w‖ ≤ 2*K^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro d
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro e
  rw [hessian_apply_eq_expectationDerivative ν L hL hK hb]
  have hρ : Measurable (fun v => L v e) :=
    (ContinuousLinearMap.apply ℝ ℝ e).continuous.measurable.comp hL
  have hbound := norm_expectationDerivative_le ν _ L hρ hL (mul_nonneg hK (norm_nonneg _)) hK
    (directionalObservable_bound ν L hb e) w
  exact ((expectationDerivative ν (fun v => L v e) L w).le_opNorm d).trans
    ((mul_le_mul_of_nonneg_right hbound (norm_nonneg _)).trans_eq (by ring))

omit [DecidableEq ι] in
theorem second_fderiv_logPartition (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (w : EuclideanSpace ℝ ι) :
    fderiv ℝ (fderiv ℝ (logPartition ν L)) w = hessian ν L w := by
  have heq : fderiv ℝ (logPartition ν L) = score ν L :=
    funext (fun y => (logPartition_hasFDerivAt ν L hL hK hb y).fderiv)
  rw [heq]
  rfl

end
end SlowEquilibration.GaussianSpinInterpolation
