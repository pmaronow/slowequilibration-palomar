-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLogPartitionTilt

@[expose] public section

/-! # Literal Gibbs tilt of a deterministic spherical potential -/
namespace SlowEquilibration.SphericalForm
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalModel GaussianSpinInterpolation
open scoped Topology ENNReal
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ} {ι : Type*} [Fintype ι]

/-- The exact unnormalized Gaussian exponential moment against a true
physical Gibbs law is the ratio of the two literal sphere partitions. -/
theorem gaussianMoment_gibbs_eq_ratio (hN : 1≤N) {A : Vector N → ℝ} (hA : Continuous A)
    (L : Vector N → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (w : EuclideanSpace ℝ ι) :
    GaussianSpinInterpolation.moment (gibbsLaw N 1 A) (fun _ => 1) L w=
      partition N 1 (fun u => A u+L u w)/partition N 1 A := by
  unfold GaussianSpinInterpolation.moment weight
  simp only [one_mul]
  rw [integral_gibbsLaw_eq_unnormalized hN 1 hA]
  congr 1
  unfold unnormalizedSphereIntegral partition
  apply integral_congr_ae
  exact .of_forall fun u => by simp only [one_mul,Real.exp_add]

/-- Exact equality of the generic Gaussian Gibbs measure and the physical
Gibbs law after adding the true finite coordinate field. -/
theorem gaussianGibbs_gibbs_eq (hN : 1≤N) {A : Vector N → ℝ} (hA : Continuous A)
    (L : Vector N → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hLc : ∀ w, Continuous (fun u => L u w)) (w : EuclideanSpace ℝ ι) :
    gibbsMeasure (gibbsLaw N 1 A) L w=gibbsLaw N 1 (fun u => A u+L u w) := by
  have hp : 0<partition N 1 (fun u => A u+L u w) := partition_pos hN 1 (hA.add (hLc w))
  have hρ : Measurable (fun u => ENNReal.ofReal (gibbsDensity N 1 A u)) :=
    (gibbsDensity_continuous 1 hA).measurable.ennreal_ofReal
  have ht : Measurable (fun u => ENNReal.ofReal
      (Real.exp (L u w)/(partition N 1 (fun u => A u+L u w)/partition N 1 A))) :=
    ((hLc w).measurable.exp.div_const _).ennreal_ofReal
  rw [gibbsMeasure,gaussianMoment_gibbs_eq_ratio hN hA L]
  unfold gibbsLaw
  rw [← withDensity_mul _ hρ ht]
  congr 1
  funext u
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (gibbsDensity_pos hN 1 hA u).le]
  congr 1
  rw [gibbsDensity,gibbsDensity]
  simp only [one_mul,Real.exp_add]
  field_simp [(partition_pos hN 1 hA).ne',hp.ne']

end
end SlowEquilibration.SphericalForm
