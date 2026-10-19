-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianSpinLogConvex
public import OAI.Probability.GaussianPropeller.SmoothedConcavity

/-!
# Smooth Ehrhard concavity for literal spin partitions

This adapter supplies all derivative hypotheses of the smooth Ehrhard
maximum-principle theorem from bounded physical spin features. In particular,
the derivative and Hessian bounds are proved for the actual integral partition;
they are not additional analytic assumptions.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.GaussianSpinInterpolation

open MeasureTheory ProbabilityTheory Set
open scoped Topology RealInnerProductSpace

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace V]

/-- Convexity in all disorder coordinates of the literal integral log partition. -/
theorem logPartition_convex (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) :
    ConvexOn ℝ univ (logPartition ν L) := by
  refine ⟨convex_univ, ?_⟩
  intro w _ v _ a b ha hb' hab
  have h := (logPartition_line_convex ν L hL hK hb w (v-w)).2
    (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ)) ha hb' hab
  simp only [smul_eq_mul, mul_zero, mul_one, zero_smul, add_zero, zero_add, one_smul, add_sub_cancel] at h
  have heq : w + b • (v-w) = a • w + b • v := by
    have he : b = 1-a := by linarith
    rw [he]
    module
  simpa only [heq, smul_eq_mul] using h

/-- The affine epigraph transform used in the Gaussian smoothing argument. -/
def affineLogPartition (ν : Measure V)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (b : EuclideanSpace ℝ ι →L[ℝ] ℝ) (a : ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  a * (b x - logPartition ν L x)

/-- Smooth Ehrhard applies to the actual affine log-partition transform, with
all regularity and global derivative bounds discharged internally. -/
theorem qheat_affineLogPartition_concave (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (b : EuclideanSpace ℝ ι →L[ℝ] ℝ) {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) :
    ConcaveOn ℝ univ
      (OAI.GaussianPropeller.EhrhardSmooth.qheat (affineLogPartition ν L b a) T) := by
  let R := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm
  let g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι :=
    fun x => R (a • (b - score ν L x))
  let H : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    fun x => R.toContinuousLinearEquiv.toContinuousLinearMap.comp (a • (-hessian ν L x))
  have hf (x : EuclideanSpace ℝ ι) :
      HasFDerivAt (affineLogPartition ν L b a) (innerSL ℝ (g x)) x := by
    have h := (b.hasFDerivAt.sub (logPartition_hasFDerivAt ν L hL hK hb x)).const_mul a
    convert h using 1
    · rfl
    · exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).apply_symm_apply _
  have hg (x : EuclideanSpace ℝ ι) : HasFDerivAt g (H x) x := by
    apply R.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp x
    have hd := (((hasFDerivAt_const b x).sub
      (score_hasFDerivAt ν L hL hK hb x)).const_smul a)
    convert hd using 1
    simp only [zero_sub]
  have hcH : Continuous H := by
    have hc := (score_contDiff ν L hL hK hb).continuous_fderiv (by norm_num)
    change Continuous (fun x => R.toContinuousLinearEquiv.toContinuousLinearMap.comp (a • (-fderiv ℝ (score ν L) x)))
    fun_prop
  have hG (x : EuclideanSpace ℝ ι) : ‖g x‖ ≤ a * (‖b‖ + K) := by
    dsimp [g]
    rw [R.norm_map, norm_smul, Real.norm_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left
      ((norm_sub_le _ _).trans (add_le_add le_rfl (norm_score_le ν L hL hK hb x))) ha
  have hH (x : EuclideanSpace ℝ ι) :
      ‖H x‖ ≤ ‖R.toContinuousLinearEquiv.toContinuousLinearMap‖ * (a * (2*K^2)) := by
    dsimp [H]
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    rw [norm_smul, norm_neg, Real.norm_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (norm_hessian_le ν L hL hK hb x) ha) (norm_nonneg _)
  have hconc : ConcaveOn ℝ univ (affineLogPartition ν L b a) := by
    exact ConcaveOn.smul ha ((b.toLinearMap.concaveOn convex_univ).sub
      (logPartition_convex ν L hL hK hb))
  apply OAI.GaussianPropeller.EhrhardSmooth.qheat_concave hf hg hcH
    (L := (a * (‖b‖ + K)).toNNReal) (D := ‖R.toContinuousLinearEquiv.toContinuousLinearMap‖ * (a * (2*K^2)))
    (fun x => ?_) hH hconc hT
  rw [Real.coe_toNNReal _ (mul_nonneg ha (add_nonneg (norm_nonneg _) hK))]
  exact hG x

/-- A linear enlargement of disorder space, including the extra independent
Gaussian coordinate, preserves the internally verified Ehrhard hypotheses. -/
theorem qheat_linear_affineLogPartition_concave {κ : Type*} [Fintype κ]
    (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ)
    (b : EuclideanSpace ℝ ι →L[ℝ] ℝ) {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) :
    ConcaveOn ℝ univ (OAI.GaussianPropeller.EhrhardSmooth.qheat
      (fun x => a * (b x - logPartition ν L (A x))) T) := by
  let L' : V → EuclideanSpace ℝ ι →L[ℝ] ℝ := fun v => (L v).comp A
  have hL' : Measurable L' := by dsimp [L']; fun_prop
  have hb' : ∀ᵐ v ∂ν, ‖L' v‖ ≤ K*‖A‖ := by
    filter_upwards [hb] with v hv
    exact ((L v).opNorm_comp_le A).trans (mul_le_mul_of_nonneg_right hv (norm_nonneg _))
  have heq : affineLogPartition ν L' b a =
      (fun x => a * (b x - logPartition ν L (A x))) := by
    funext x
    simp only [affineLogPartition, logPartition, moment, weight, L',
      ContinuousLinearMap.comp_apply]
  simpa only [heq] using qheat_affineLogPartition_concave ν L' hL'
    (mul_nonneg hK (norm_nonneg _)) hb' b ha hT

end SlowEquilibration.GaussianSpinInterpolation
