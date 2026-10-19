-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianSpinSmoothEhrhard
public import SlowEquilibration.GaussianEpigraphHeat
public import SlowEquilibration.GaussianNoisyLowerTail

/-! A variance-sensitive lower tail for the literal Gaussian spin partition.
All smooth Ehrhard hypotheses and the smoothed-quantile concavity are proved
from bounded physical spin features. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.GaussianSpinInterpolation

open MeasureTheory ProbabilityTheory Set
open scoped Topology RealInnerProductSpace
open GaussianExtraCoordinate GaussianEpigraphHeat
open OAI.GaussianPropeller.Quantile OAI.GaussianPropeller.EhrhardSmooth

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace V]

/-- Concavity of the quantile of the independently smoothed physical pressure. -/
theorem logPartition_smoothed_quantile_concave
    (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) :
    ConcaveOn ℝ univ (fun s : ℝ =>
      q (∫ z, Φ (s - logPartition ν L z) ∂stdGaussian (EuclideanSpace ℝ ι))) := by
  have hc := (logPartition_contDiff ν L hL hK hb).continuous
  have he := qheat_linear_affineLogPartition_concave (ι := ι ⊕ Unit)
    ν L hL hK hb (Real.sqrt 2 • projection) extra
    (by positivity : (0:ℝ) ≤ Real.sqrt 2) (by norm_num : (0:ℝ) ≤ 1/2)
  change ConcaveOn ℝ univ
    (qheat (epigraphTransform (logPartition ν L)) (1/2)) at he
  let B : ℝ →ₗ[ℝ] EuclideanSpace ℝ (ι ⊕ Unit) :=
    (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (EuclideanSpace.single (.inr ()) 1)
  have hB (s : ℝ) : B s = EuclideanSpace.single (.inr ()) s := by
    ext j
    change s * (EuclideanSpace.single (.inr ()) (1 : ℝ)) j =
      (EuclideanSpace.single (.inr ()) s) j
    simp only [PiLp.single_apply]
    split_ifs <;> simp
  have h := he.comp_linearMap B
  have hid : (qheat (epigraphTransform (logPartition ν L)) (1/2) ∘ B) =
      fun s : ℝ => q (∫ z, Φ (s - logPartition ν L z)
        ∂stdGaussian (EuclideanSpace ℝ ι)) := by
    funext s
    simp only [Function.comp_apply, hB, qheat,
      heat_epigraphTransform (logPartition ν L) hc s]
  simpa only [preimage_univ, hid] using h

omit [DecidableEq ι] in
/-- The physical logarithmic partition has finite Gaussian second moment. -/
theorem logPartition_gaussian_memLp_two
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) :
    MemLp (logPartition ν L) 2 (stdGaussian (EuclideanSpace ℝ ι)) := by
  have hc := (logPartition_contDiff ν L hL hK hb).continuous
  have hn : MemLp (fun w : EuclideanSpace ℝ ι => K * ‖w‖) 2
      (stdGaussian (EuclideanSpace ℝ ι)) :=
    (IsGaussian.memLp_two_id (μ := stdGaussian (EuclideanSpace ℝ ι))).norm.const_mul K
  apply hn.mono' hc.aestronglyMeasurable
  exact .of_forall fun w => by
    rw [Real.norm_eq_abs]
    exact abs_logPartition_le ν L hL hb w

/-- Universal variance-sensitive lower tail of the literal coefficient partition.
No asymptotic free-energy, external concentration, or quantile-concavity input
is assumed. -/
theorem logPartition_gaussian_lower_tail
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) {u : ℝ}
    (hu : 8 * Real.sqrt (variance (logPartition ν L)
      (stdGaussian (EuclideanSpace ℝ ι)) + 1) ≤ u) :
    (stdGaussian (EuclideanSpace ℝ ι)).real
      {z | logPartition ν L z ≤
        (∫ w, logPartition ν L w ∂stdGaussian (EuclideanSpace ℝ ι)) - u} ≤
      Real.exp (-u^2 / (64 * (variance (logPartition ν L)
        (stdGaussian (EuclideanSpace ℝ ι)) + 1))) := by
  exact GaussianNoisyLowerTail.lower_tail_of_concave_smoothed_quantile
    (stdGaussian (EuclideanSpace ℝ ι)) (logPartition ν L)
    (logPartition_contDiff ν L hL hK hb).continuous.measurable
    (logPartition_gaussian_memLp_two ν L hL hK hb)
    (logPartition_smoothed_quantile_concave ν L hL hK hb) hu

end SlowEquilibration.GaussianSpinInterpolation
