module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalBarycenterLaw
public import SlowEquilibration.SphereSupportedIntegrals
public import SlowEquilibration.MeasureCovariance

@[expose] public section

/-! # Exact one- and two-replica identities for the actual barycenter -/
namespace SlowEquilibration.SphericalBarycenter
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000
open Set MeasureTheory ProbabilityTheory Filter Metric
open SphericalModel SphericalForm SphericalAging.HardSphereDynamics
open scoped Topology ContDiff InnerProductSpace BigOperators ENNReal
variable {N : ℕ}

/-- The alignment is exactly the actual reweighted overlap mean. -/
theorem barycenter_alignment_eq (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (x : Vector N) :
    inner ℝ (spin x) (barycenter β H h x) =
      ∫ u, overlap x u ∂weightedLaw β H h x := by
  let := weightedLaw_probability hN β hH hh x
  have hi := integrable_sphereSupported_continuous (weightedLaw β H h x)
    (weightedLaw_support hN β H h x) spin_contDiff.continuous
  rw [barycenter_eq_integral hN β hH hh x]
  have he := (innerSL ℝ (spin x)).integral_comp_comm hi
  change (∫ u, inner ℝ (spin x) (spin u) ∂weightedLaw β H h x) =
    inner ℝ (spin x) (∫ u, spin u ∂weightedLaw β H h x) at he
  rw [← he]
  simp_rw [spin_inner hN]

/-- The squared norm is exactly the true two-replica overlap integral. -/
theorem barycenter_norm_sq_eq (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (x : Vector N) :
    ‖barycenter β H h x‖^2 =
      ∫ z : Vector N × Vector N, overlap z.1 z.2
        ∂(weightedLaw β H h x).prod (weightedLaw β H h x) := by
  let := weightedLaw_probability hN β hH hh x
  have hi := integrable_sphereSupported_continuous (weightedLaw β H h x)
    (weightedLaw_support hN β H h x) spin_contDiff.continuous
  have he := integral_prod_bilin
    (innerSL ℝ : Vector N →L[ℝ] Vector N →L[ℝ] ℝ) hi hi
  change (∫ z : Vector N × Vector N, inner ℝ (spin z.1) (spin z.2)
    ∂(weightedLaw β H h x).prod (weightedLaw β H h x)) =
      inner ℝ (∫ u, spin u ∂weightedLaw β H h x)
        (∫ u, spin u ∂weightedLaw β H h x) at he
  simp_rw [spin_inner hN] at he
  rw [← barycenter_eq_integral hN β hH hh x, real_inner_self_eq_norm_sq] at he
  exact he.symm

/-- The actual centered spin variance is precisely one minus the squared
norm of the constructed barycenter. -/
theorem weighted_spin_variance (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (x : Vector N) :
    (∫ u, ‖spin u-barycenter β H h x‖^2 ∂weightedLaw β H h x) =
      1-‖barycenter β H h x‖^2 := by
  let := weightedLaw_probability hN β hH hh x
  have hu := memLp_sphereSupported_continuous (weightedLaw β H h x)
    (weightedLaw_support hN β H h x) spin_contDiff.continuous 2
  have he := MeasureCovariance.integral_norm_sub_mean_sq (weightedLaw β H h x) spin hu
  rw [← barycenter_eq_integral hN β hH hh x] at he
  have hnorm : (∫ u, ‖spin u‖^2 ∂weightedLaw β H h x) = 1 := by
    have ha : (fun u => ‖spin u‖^2) =ᵐ[weightedLaw β H h x] (fun _ => (1:ℝ)) := by
      filter_upwards [weightedLaw_support hN β H h x] with u hu
      rw [spin_norm hN u ((onSphere_iff_norm_sq u).mpr hu), one_pow]
    rw [integral_congr_ae ha]
    simp
  rw [hnorm] at he
  exact he

end
end SlowEquilibration.SphericalBarycenter
