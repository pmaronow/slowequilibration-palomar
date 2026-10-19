module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalBarycenterMeans
public import SlowEquilibration.SphericalBarycenterWeightDifferential
public import SlowEquilibration.ScalarNormalizedDerivative
public import SlowEquilibration.SphericalObservableDisplacement

@[expose] public section

/-! # Genuine normalized Gibbs differentiation and barycenter covariance -/
namespace SlowEquilibration.SphericalBarycenter
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000
open Set MeasureTheory Filter Metric
open SphericalModel SphericalForm SphericalAging.HardSphereDynamics
open scoped Topology ContDiff InnerProductSpace BigOperators
variable {N : ℕ}

private lemma quotient_covariance_algebra (d n A B : ℝ) :
    d⁻¹*(2*A)+n*(-(d^2)⁻¹*(2*B)) = 2*(d⁻¹*(A-(d⁻¹*n)*B)) := by
  rw [← inv_pow]
  ring

set_option backward.isDefEq.respectTransparency.types true in
/-- The normalized derivative is the actual score covariance. -/
theorem scalarAverage_fderiv_apply (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {a : Vector N → ℝ} (ha : ContDiff ℝ ∞ a) (x v : Vector N) :
    (fderiv ℝ (scalarAverage β H h a) x) v =
      2*∫ u, (a u-scalarAverage β H h a x)*
        (fderiv ℝ (fun y => logPsi h y u) x) v ∂weightedLaw β H h x := by
  have hp := denominator_pos hN β hH hh x
  change fderiv ℝ (fun y => (denominator β H h y)⁻¹*scalarNumerator β H h a y) x v = _
  conv_lhs => rw [scalar_normalized_fderiv_apply (denominator β H h) (scalarNumerator β H h a) x v
    (((denominator_contDiff hN β hH hh).differentiable (by simp)) x)
    (((scalarNumerator_contDiff hN β hH hh ha).differentiable (by simp)) x) hp.ne']
  conv_lhs => rw [scalarNumerator_fderiv_apply hN β hH hh ha x v, denominator_fderiv_apply hN β hH hh x v]
  conv_rhs => rw [integral_weightedLaw hN β hH hh x]
  simp only [smul_eq_mul]
  have hD : Continuous (fun u => (fderiv ℝ (fun y => logPsi h y u) x) v) :=
    (fderiv_logPsi_continuous hN hh x).clm_apply continuous_const
  have hP : Continuous (fun u : Vector N => (psi h x u)^2) :=
    ((psi_joint_contDiff hh).continuous.comp (continuous_id.prodMk continuous_const)).pow 2
  have hprod : (fun u => (psi h x u)^2*((a u-scalarAverage β H h a x)*
      (fderiv ℝ (fun y => logPsi h y u) x) v)) =
      fun u => (psi h x u)^2*a u*(fderiv ℝ (fun y => logPsi h y u) x) v-
        scalarAverage β H h a x*((psi h x u)^2*(fderiv ℝ (fun y => logPsi h y u) x) v) := by
    funext u; ring
  have hI₁ : Integrable (fun u => (psi h x u)^2*a u*(fderiv ℝ (fun y => logPsi h y u) x) v)
      (gibbsLaw N β H) := by
    convert! integrable_gibbs_of_continuous hN β hH ((hP.mul ha.continuous).mul hD) using 1
  have hI₂ : Integrable (fun u => scalarAverage β H h a x*((psi h x u)^2*
      (fderiv ℝ (fun y => logPsi h y u) x) v)) (gibbsLaw N β H) := by
    convert! (integrable_gibbs_of_continuous hN β hH (hP.mul hD)).const_mul
      (scalarAverage β H h a x) using 1
  conv_rhs => rw [hprod, integral_sub hI₁ hI₂, integral_const_mul]
  simp only [scalarAverage]
  convert! quotient_covariance_algebra (denominator β H h x) (scalarNumerator β H h a x)
    (∫ u, (psi h x u)^2*a u*(fderiv ℝ (fun y => logPsi h y u) x) v ∂gibbsLaw N β H)
    (∫ u, (psi h x u)^2*(fderiv ℝ (fun y => logPsi h y u) x) v ∂gibbsLaw N β H) using 1

/-- Each literal barycenter coordinate is the normalized spin moment. -/
lemma barycenter_coordinate_eq (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (i : Fin N) :
    (fun x => barycenter β H h x i) = scalarAverage β H h (fun u => spin u i) := by
  funext x
  let := weightedLaw_probability hN β hH hh x
  rw [barycenter_eq_integral hN β hH hh x, scalarAverage_eq_integral hN β hH hh]
  have hi := integrable_sphereSupported_continuous (weightedLaw β H h x)
    (weightedLaw_support hN β H h x) spin_contDiff.continuous
  exact ((PiLp.proj 2 (fun _ : Fin N => ℝ) i : Vector N →L[ℝ] ℝ).integral_comp_comm hi).symm

/-- The actual tangent gradient rows equal the source's actual spin-score
covariance, with every differentiation and normalization derived above. -/
theorem barycenter_surfaceGradient (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (x : Vector N) (i : Fin N) :
    surfaceGradient (fun y => barycenter β H h y i) x =
      (2:ℝ) • ∫ u, (spin u i-barycenter β H h x i) • score h x u ∂weightedLaw β H h x := by
  let := weightedLaw_probability hN β hH hh x
  have ha : ContDiff ℝ ∞ (fun u : Vector N => spin u i) :=
    (show ContDiff ℝ ∞ (fun v : Vector N => v i) from
      (PiLp.proj 2 (fun _ : Fin N => ℝ) i : Vector N →L[ℝ] ℝ).contDiff).comp spin_contDiff
  have hI : Integrable (fun u => (spin u i-barycenter β H h x i) • score h x u)
      (weightedLaw β H h x) := integrable_sphereSupported_continuous (weightedLaw β H h x)
    (weightedLaw_support hN β H h x)
    ((ha.continuous.sub continuous_const).smul (score_continuous hN hh x))
  apply ext_inner_right ℝ
  intro v
  rw [inner_surfaceGradient, barycenter_coordinate_eq hN β hH hh i,
    scalarAverage_fderiv_apply hN β hH hh ha x (tangentProjection x v)]
  have he := (innerSL ℝ v).integral_comp_comm hI
  change (∫ u, inner ℝ v ((spin u i-barycenter β H h x i) • score h x u)
    ∂weightedLaw β H h x) = inner ℝ v (∫ u,
      (spin u i-barycenter β H h x i) • score h x u ∂weightedLaw β H h x) at he
  rw [real_inner_smul_left, real_inner_comm, ← he]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro u
  change (spin u i-scalarAverage β H h (fun u => spin u i) x)*
    (fderiv ℝ (fun y => logPsi h y u) x) (tangentProjection x v) =
      inner ℝ v ((spin u i-barycenter β H h x i) • score h x u)
  rw [real_inner_smul_right, real_inner_comm, score, inner_surfaceGradient]
  congr 1
  rw [← barycenter_coordinate_eq hN β hH hh i]

end
end SlowEquilibration.SphericalBarycenter
