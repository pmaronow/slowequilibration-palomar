module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalBarycenterDifferential

@[expose] public section

/-! # Genuine covariance and Hilbert--Schmidt bounds for the actual barycenter -/
namespace SlowEquilibration.SphericalBarycenter
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter Metric
open SphericalModel SphericalForm SphericalAging.HardSphereDynamics
open scoped Topology ContDiff InnerProductSpace BigOperators
variable {N : ℕ}

/-- The squared Hilbert--Schmidt norm is bounded by four times the actual
weighted score energy, using the actual centered spin variance ≤1. -/
theorem barycenter_jacobian_le_score (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (x : Vector N) :
    surfaceJacobianNormSq (barycenter β H h) x ≤
      4*∫ u, ‖score h x u‖^2 ∂weightedLaw β H h x := by
  let := weightedLaw_probability hN β hH hh x
  have hs := memLp_sphereSupported_continuous (weightedLaw β H h x)
    (weightedLaw_support hN β H h x) (score_continuous hN hh x) 2
  have hc (i : Fin N) : Continuous (fun u : Vector N => spin u i-barycenter β H h x i) :=
    (((PiLp.proj 2 (fun _ : Fin N => ℝ) i : Vector N →L[ℝ] ℝ).continuous).comp
      spin_contDiff.continuous).sub continuous_const
  have hm (i : Fin N) := memLp_sphereSupported_continuous (weightedLaw β H h x)
    (weightedLaw_support hN β H h x) (hc i) 2
  have hr (i : Fin N) : ‖surfaceGradient (fun y => barycenter β H h y i) x‖^2 ≤
      4*(∫ u, (spin u i-barycenter β H h x i)^2 ∂weightedLaw β H h x)*
        (∫ u, ‖score h x u‖^2 ∂weightedLaw β H h x) := by
    rw [barycenter_surfaceGradient hN β hH hh x i, norm_smul,
      Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2), mul_pow]
    have hv := MeasureCovariance.norm_integral_smul_sq_le (weightedLaw β H h x)
      (fun u => spin u i-barycenter β H h x i) (score h x) (hm i) hs
    convert! mul_le_mul_of_nonneg_left hv (by norm_num : (0:ℝ) ≤ 4) using 1 <;> ring
  have hsum : (∑ i : Fin N, ∫ u, (spin u i-barycenter β H h x i)^2 ∂weightedLaw β H h x) =
      1-‖barycenter β H h x‖^2 := by
    rw [← integral_finsetSum Finset.univ (fun i _ => (hm i).integrable_sq)]
    have he : (fun u => ∑ i : Fin N, (spin u i-barycenter β H h x i)^2) =
        fun u => ‖spin u-barycenter β H h x‖^2 := by
      funext u
      simp only [PiLp.norm_sq_eq_of_L2, PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
    rw [he, weighted_spin_variance hN β hH hh x]
  have hE : 0 ≤ ∫ u, ‖score h x u‖^2 ∂weightedLaw β H h x := integral_nonneg (fun _ => sq_nonneg _)
  calc
    _ ≤ ∑ i : Fin N, 4*(∫ u, (spin u i-barycenter β H h x i)^2 ∂weightedLaw β H h x)*
        (∫ u, ‖score h x u‖^2 ∂weightedLaw β H h x) := Finset.sum_le_sum (fun i _ => hr i)
    _ = 4*(1-‖barycenter β H h x‖^2)*
        (∫ u, ‖score h x u‖^2 ∂weightedLaw β H h x) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, hsum]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg ‖barycenter β H h x‖]) hE

/-- The weighted score energy is exactly the actual ψ-gradient energy
normalized by the source's actual denominator. -/
theorem weighted_score_energy (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (x : Vector N) :
    (∫ u, ‖score h x u‖^2 ∂weightedLaw β H h x) =
      (denominator β H h x)⁻¹*
        ∫ u, ‖surfaceGradient (fun y => psi h y u) x‖^2 ∂gibbsLaw N β H := by
  conv_lhs => rw [integral_weightedLaw hN β hH hh x]
  simp only [smul_eq_mul]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro u
  change (psi h x u)^2*‖score h x u‖^2 = ‖surfaceGradient (fun y => psi h y u) x‖^2
  rw [psi_surfaceGradient hN hh, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- The first literal source Hilbert--Schmidt estimate. -/
theorem barycenter_jacobian_le_weight_energy (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (x : Vector N) :
    surfaceJacobianNormSq (barycenter β H h) x ≤
      (4/denominator β H h x)*
        ∫ u, ‖surfaceGradient (fun y => psi h y u) x‖^2 ∂gibbsLaw N β H := by
  have he := barycenter_jacobian_le_score hN β hH hh x
  rw [weighted_score_energy hN β hH hh x] at he
  convert! he using 1 <;> ring

/-- The global source bound 4NM² is proved from the literal weight and
true spherical geometry, rather than assumed for the barycenter. -/
theorem barycenter_jacobian_le (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (M : ℝ) (hM : 0 ≤ M)
    (hd : ∀ r ∈ Icc (-1:ℝ) 1, |deriv h r| ≤ M) (x : Vector N) (hx : OnSphere x) :
    surfaceJacobianNormSq (barycenter β H h) x ≤ 4*(N:ℝ)*M^2 := by
  let := weightedLaw_probability hN β hH hh x
  have hi := (memLp_sphereSupported_continuous (weightedLaw β H h x)
    (weightedLaw_support hN β H h x) (score_continuous hN hh x) 2).integrable_norm_pow'
  have hp := integral_mono_ae hi (integrable_const ((N:ℝ)*M^2)) (by
    filter_upwards [weightedLaw_support hN β H h x] with u hu
    exact score_norm_sq_le hN hh M hM hd x u hx ((onSphere_iff_norm_sq u).mpr hu))
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hp
  have he := barycenter_jacobian_le_score hN β hH hh x
  have hm := mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ) ≤ 4)
  exact he.trans (by convert! hm using 1 <;> ring)

end
end SlowEquilibration.SphericalBarycenter
