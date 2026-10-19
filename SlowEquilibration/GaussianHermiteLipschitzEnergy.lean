-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianHermiteSmoothIBP

/-! The weighted Hermite energy of an actual Euclidean Lipschitz function
is bounded by the square of its Euclidean Lipschitz constant. The coordinate
identification introduces no dimension factor in this energy estimate. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.GaussianHermiteDerivative

open MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open scoped BigOperators NNReal Topology

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The raising identity combined with the actual Euclidean gradient bound
gives the dimension-free weighted-energy estimate. -/
theorem finite_weighted_energy_le_lipschitz_square
    (f : EuclideanSpace ℝ ι → ℝ) (hf : ContDiff ℝ 1 f)
    (L : ℝ≥0) (hlip : LipschitzWith L f)
    (hf2 : MemLp (fun x : ι → ℝ => f (WithLp.toLp 2 x)) 2 (γpi ι))
    (s : Finset (ι → ℕ)) :
    ∑ a ∈ s, (degree a : ℝ) *
        (coeff (fun x : ι → ℝ => f (WithLp.toLp 2 x)) a) ^ 2 ≤ (L : ℝ) ^ 2 := by
  let T := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  let F : (ι → ℝ) → ℝ := fun x => f (WithLp.toLp 2 x)
  have hF : ContDiff ℝ 1 F := hf.comp T.contDiff
  have hgrad (x : EuclideanSpace ℝ ι) : ‖gradient f x‖ ≤ (L : ℝ) := by
    rw [gradient, LinearIsometryEquiv.norm_map]
    exact norm_fderiv_le_of_lipschitz ℝ hlip
  have hpartial (x : ι → ℝ) (i : ι) :
      coordinatePartial F i x = (gradient f (WithLp.toLp 2 x)) i :=
    (SYK.gradient_toLp_coord_eq_fderiv f (hf.differentiable (by norm_num)) x i).symm
  have hsum (x : ι → ℝ) :
      (∑ i, (coordinatePartial F i x) ^ 2) ≤ (L : ℝ) ^ 2 := by
    simp_rw [hpartial]
    have he : (∑ i, ((gradient f (WithLp.toLp 2 x)) i) ^ 2) =
        ‖gradient f (WithLp.toLp 2 x)‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      simp only [Real.norm_eq_abs, sq_abs]
    rw [he]
    exact pow_le_pow_left₀ (norm_nonneg _) (hgrad _) 2
  have hdb (x : ι → ℝ) (i : ι) : |coordinatePartial F i x| ≤ (L : ℝ) := by
    have hs : (coordinatePartial F i x) ^ 2 ≤ (L : ℝ) ^ 2 :=
      (Finset.single_le_sum (fun j _ => sq_nonneg (coordinatePartial F j x))
        (Finset.mem_univ i)).trans (hsum x)
    nlinarith [abs_nonneg (coordinatePartial F i x),
      sq_abs (coordinatePartial F i x), L.coe_nonneg]
  have hdf2 (i : ι) : MemLp (coordinatePartial F i) 2 (γpi ι) := by
    apply (memLp_const (L : ℝ)).mono
      (((hF.continuous_fderiv (by norm_num)).clm_apply continuous_const).aestronglyMeasurable)
    exact .of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg L.coe_nonneg, coordinatePartial] using hdb x i
  have hjet : ExponentialFirstJet F :=
    ExponentialFirstJet.of_lipschitz F hF _ (hlip.comp T.toContinuousLinearMap.lipschitzWith)
  apply (finite_weighted_energy_le F hjet hf2 hdf2 s).trans
  rw [← integral_finsetSum Finset.univ (fun i _ => (hdf2 i).integrable_sq)]
  calc
    _ ≤ ∫ _x : ι → ℝ, (L : ℝ) ^ 2 ∂γpi ι :=
      integral_mono (integrable_finsetSum _ (fun i _ => (hdf2 i).integrable_sq))
        (integrable_const _) (hsum)
    _ = (L : ℝ) ^ 2 := by simp

end SlowEquilibration.GaussianHermiteDerivative
