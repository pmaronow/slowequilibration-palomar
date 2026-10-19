-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianSpinLogConvex
public import SlowEquilibration.SphericalWeightedGibbsNormalization

@[expose] public section

/-! # Literal spherical coefficient-line log partition

A deterministic continuous source penalty is absorbed into a true Gibbs
spin measure. The exact partition ratio connects the ordinary source
integral to the variance-based coefficient-line convexity theorem.
-/
namespace SlowEquilibration.SphericalForm
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalModel GaussianSpinInterpolation
open SphericalAging.HardSphereDynamics
open scoped Topology
set_option maxHeartbeats 950000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Exact Gibbs normalization of a logarithmic coefficient observation. -/
theorem logPartition_gibbs_eq_ratio (hN : 1 ≤ N) {A : Vector N → ℝ} (hA : Continuous A)
    (L : Vector N → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hLc : ∀ w,Continuous (fun u => L u w)) (w : EuclideanSpace ℝ ι) :
    GaussianSpinInterpolation.logPartition (gibbsLaw N 1 A) L w=
      Real.log (partition N 1 (fun u => A u+L u w))-Real.log (partition N 1 A) := by
  unfold GaussianSpinInterpolation.logPartition GaussianSpinInterpolation.moment weight
  simp only [one_mul]
  rw [integral_gibbsLaw_eq_unnormalized hN 1 hA]
  have he : unnormalizedSphereIntegral 1 A (fun u => Real.exp (L u w))=
      partition N 1 (fun u => A u+L u w) := by
    unfold unnormalizedSphereIntegral partition
    apply integral_congr_ae
    exact .of_forall fun u => by
      change Real.exp (1*A u)*Real.exp (L u w)=Real.exp (1*(A u+L u w))
      rw [one_mul,one_mul,Real.exp_add]
  rw [he]
  have hp : 0 < partition N 1 (fun u => A u+L u w) :=
    partition_pos hN 1 (hA.add (hLc w))
  exact Real.log_div hp.ne' (partition_pos hN 1 hA).ne'

/-- Actual source integrals with deterministic smooth penalties are convex
along every finite coefficient line. All measures are genuine sphere Gibbs
laws; positivity and the Hessian variance enter internally. -/
theorem spherical_logPartition_line_convex (hN : 1 ≤ N) {A : Vector N → ℝ}
    (hA : Continuous A) (L : Vector N → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hL : Measurable L) (hLc : ∀ w,Continuous (fun u => L u w))
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ u,OnSphere u → ‖L u‖ ≤ K)
    (w d : EuclideanSpace ℝ ι) :
    ConvexOn ℝ univ (fun t : ℝ => Real.log (partition N 1 (fun u => A u+L u (w+t • d)))) := by
  let _ := gibbsLaw_probability hN 1 hA
  have hBound : ∀ᵐ u ∂gibbsLaw N 1 A,‖L u‖ ≤ K := by
    filter_upwards [gibbsLaw_support hN 1 A] with u hu
    exact hb u ((onSphere_iff_norm_sq u).mpr hu)
  have h := logPartition_line_convex (gibbsLaw N 1 A) L hL hK hBound w d
  have he : (fun t : ℝ => Real.log (partition N 1 (fun u => A u+L u (w+t • d))))=
      fun t => GaussianSpinInterpolation.logPartition (gibbsLaw N 1 A) L (w+t • d)+Real.log (partition N 1 A) := by
    funext t
    rw [logPartition_gibbs_eq_ratio hN hA L hLc]
    ring
  rw [he]
  exact h.add_const _

end
end SlowEquilibration.SphericalForm
