-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianExtraCoordinate
public import SlowEquilibration.GaussianQuantileConvolution

@[expose] public section

noncomputable section

namespace SlowEquilibration.GaussianEpigraphHeat

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open GaussianExtraCoordinate GaussianQuantileConvolution
open OAI.GaussianPropeller.Quantile OAI.GaussianPropeller.HeatConvolution

variable {ι : Type*} [Fintype ι]

/-- The smooth epigraph transform, with one independent Gaussian coordinate. -/
def epigraphTransform (F : EuclideanSpace ℝ ι → ℝ)
    (x : EuclideanSpace ℝ (ι ⊕ Unit)) : ℝ :=
  Real.sqrt 2 * (extra x - F (Real.sqrt 2 • projection x))

/-- Half-time heat smoothing of the epigraph transform is the noisy CDF. -/
theorem heat_epigraphTransform [DecidableEq ι]
    (F : EuclideanSpace ℝ ι → ℝ) (hF : Continuous F) (s : ℝ) :
    heat (fun y => Φ (epigraphTransform F y)) (1/2)
        (EuclideanSpace.single (.inr ()) s) =
      ∫ z, Φ (s - F z) ∂stdGaussian (EuclideanSpace ℝ ι) := by
  let H : EuclideanSpace ℝ ι × ℝ → ℝ :=
    fun p => Φ (Real.sqrt 2 * (s - F p.1) + p.2)
  have hH : Integrable H ((stdGaussian (EuclideanSpace ℝ ι)).prod (gaussianReal 0 1)) :=
    integrable_Φ_comp (by fun_prop)
  have hsqrt : Real.sqrt 2 * Real.sqrt (1/2 : ℝ) = 1 := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hpoint (z : EuclideanSpace ℝ (ι ⊕ Unit)) :
      Φ (epigraphTransform F (EuclideanSpace.single (.inr ()) s +
        Real.sqrt (1/2 : ℝ) • z)) = H (projection z, extra z) := by
    congr 1
    dsimp only [epigraphTransform, H]
    simp only [map_add, map_smul, projection_single_extra, extra_single_extra,
      zero_add, smul_smul, hsqrt, one_smul, smul_eq_mul]
    nlinarith only [congrArg (fun a : ℝ => a * extra z) hsqrt]
  have hmap : AEStronglyMeasurable H
      ((stdGaussian (EuclideanSpace ℝ (ι ⊕ Unit))).map (fun x => (projection x, extra x))) := by
    rw [map_split_stdGaussian]
    exact hH.aestronglyMeasurable
  have hm := integral_map
    (by fun_prop : AEMeasurable (fun x : EuclideanSpace ℝ (ι ⊕ Unit) =>
      (projection x, extra x)) (stdGaussian (EuclideanSpace ℝ (ι ⊕ Unit)))) hmap
  rw [map_split_stdGaussian] at hm
  unfold heat
  calc
    _ = ∫ z, H (projection z, extra z) ∂stdGaussian (EuclideanSpace ℝ (ι ⊕ Unit)) :=
      integral_congr_ae (ae_of_all _ hpoint)
    _ = ∫ p, H p ∂((stdGaussian (EuclideanSpace ℝ ι)).prod (gaussianReal 0 1)) := hm.symm
    _ = ∫ z, ∫ u, H (z, u) ∂gaussianReal 0 1 ∂stdGaussian (EuclideanSpace ℝ ι) :=
      integral_prod _ hH
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      dsimp only [H]
      rw [integral_Φ_add]
      congr 1
      exact mul_div_cancel_left₀ (s - F z) (Real.sqrt_ne_zero'.mpr (by norm_num))

end SlowEquilibration.GaussianEpigraphHeat
