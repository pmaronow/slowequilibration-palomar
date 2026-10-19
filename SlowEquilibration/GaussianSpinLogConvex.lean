-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianSpinHessian
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-! # Convexity of literal spin log partitions along coefficient lines

The second derivative is an actual Gibbs variance. The spin measure may be
nonatomic and need not be the uniform sphere law.
-/
namespace SlowEquilibration.GaussianSpinInterpolation
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 950000
set_option backward.isDefEq.respectTransparency false
variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace V]

/-- The actual coefficient-line second derivative is nonnegative, because
it is the variance of the corresponding genuine Gibbs observable. -/
theorem hessian_self_nonnegative (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (w d : EuclideanSpace ℝ ι) : 0 ≤ hessian ν L w d d := by
  rw [hessian_apply_covariance ν L hL hK hb]
  simpa only [pow_two] using expectation_square_sub_square_nonneg ν (fun v => L v d) L
    ((ContinuousLinearMap.apply ℝ ℝ d).continuous.measurable.comp hL) hL
    (directionalObservable_bound ν L hb d) w

/-- True convexity of the ordinary log-integral along every coefficient
line, with finite-dimensional smoothness and variance proved internally. -/
theorem logPartition_line_convex (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (w d : EuclideanSpace ℝ ι) :
    ConvexOn ℝ univ (fun t : ℝ => logPartition ν L (w+t • d)) := by
  let f := fun t : ℝ => logPartition ν L (w+t • d)
  let g := fun t : ℝ => score ν L (w+t • d) d
  have hLine (t : ℝ) : HasDerivAt (fun t : ℝ => w+t • d) d t := by
    simpa only [one_smul,id_eq] using ((hasDerivAt_id t).smul_const d).const_add w
  have hf (t : ℝ) : HasDerivAt f (g t) t := by
    exact (logPartition_hasFDerivAt ν L hL hK hb (w+t • d)).comp_hasDerivAt t (hLine t)
  have hg (t : ℝ) : HasDerivAt g (hessian ν L (w+t • d) d d) t := by
    have h := ((ContinuousLinearMap.apply ℝ ℝ d).hasFDerivAt.comp (w+t • d)
      (score_hasFDerivAt ν L hL hK hb (w+t • d))).comp_hasDerivAt t (hLine t)
    exact h
  have he : deriv f=g := funext fun t => (hf t).deriv
  apply convexOn_univ_of_deriv2_nonneg (fun t => (hf t).differentiableAt)
  · rw [he]
    exact fun t => (hg t).differentiableAt
  · intro t
    change 0 ≤ deriv (deriv f) t
    rw [he,(hg t).deriv]
    exact hessian_self_nonnegative ν L hL hK hb (w+t • d) d

end
end SlowEquilibration.GaussianSpinInterpolation
