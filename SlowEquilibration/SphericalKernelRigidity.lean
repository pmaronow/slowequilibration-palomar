module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalSmoothing
public import SlowEquilibration.SphericalWeakRigidity
public import SlowEquilibration.SphericalSmoothRigidity

@[expose] public section

/-! # Genuine zero-energy rigidity after actual spherical smoothing -/

namespace SlowEquilibration.SphericalForm
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter Metric
open SphericalModel SphericalAging.HardSphereDynamics
open SphericalAging.SphericalIntegrationByParts
open scoped InnerProductSpace Topology ContDiff

lemma gibbsToL2_inner_right {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f : Lp ℝ 2 (gibbsLaw N β H))
    (g : Vector N → ℝ) (hg : Continuous g) :
    inner ℝ f (gibbsToL2 hN β H hH g hg) = ∫ x, f x * g x ∂gibbsLaw N β H := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [gibbsToL2_coe hN β H hH g hg] with x hx
  simp [hx, RCLike.inner_apply, mul_comm]

/-- The actual signed unweighted density of a Gibbs L² element, integrated
with respect to its actual Gibbs law. -/
def gibbsUnweightedDensity {N : ℕ} (β : ℝ) (H : Vector N → ℝ)
    (f : Lp ℝ 2 (gibbsLaw N β H)) (x : Vector N) : ℝ :=
  f x * (gibbsDensity N β H x)⁻¹

lemma gibbsUnweightedDensity_integrable {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f : Lp ℝ 2 (gibbsLaw N β H)) :
    Integrable (gibbsUnweightedDensity β H f) (gibbsLaw N β H) :=
  (Lp.memLp f).integrable_mul (memLp_gibbs_of_continuous hN β hH
    ((gibbsDensity_continuous β hH).inv₀ (fun x => (gibbsDensity_pos hN β hH x).ne')))

lemma gibbsUnweightedDensity_moment {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f : Lp ℝ 2 (gibbsLaw N β H))
    (p : Vector N → ℝ) (hp : Continuous p) :
    (∫ x, gibbsUnweightedDensity β H f x * p x ∂gibbsLaw N β H) =
      inner ℝ f (gibbsToL2 hN β H hH
        (fun x => (gibbsDensity N β H x)⁻¹ * p x)
        (((gibbsDensity_continuous β hH).inv₀
          (fun x => (gibbsDensity_pos hN β hH x).ne')).mul hp)) := by
  rw [gibbsToL2_inner_right]
  congr 1
  funext x
  simp only [gibbsUnweightedDensity]
  ring

lemma skew_inner_self_zero {N : ℕ} (A : Operator N) (hA : star A = -A) (z : Vector N) :
    inner ℝ z (A z) = 0 := by
  have hi := A.adjoint_inner_left z z
  rw [← ContinuousLinearMap.star_eq_adjoint, hA] at hi
  simp only [neg_apply, inner_neg_left] at hi
  rw [real_inner_comm (A z) z] at hi
  have hj := real_inner_comm z (A z)
  linarith

lemma sphereSmoothingKernel_hasFDerivAt_formula {N : ℕ} (ε : ℝ) (x y : Vector N) :
    HasFDerivAt (fun z : Vector N => sphereSmoothingKernel ε z y)
      ((deriv Real.smoothTransition (2 * (1 - ‖x - y‖ ^ 2 / ε ^ 2)) * (-4 / ε ^ 2)) •
        innerSL ℝ (x - y)) x := by
  have hsub : HasFDerivAt (fun z : Vector N => z - y) (ContinuousLinearMap.id ℝ (Vector N)) x :=
    (hasFDerivAt_id x).sub_const y
  have harg : HasFDerivAt (fun z : Vector N => 2 * (1 - ‖z - y‖ ^ 2 / ε ^ 2))
      ((-4 / ε ^ 2) • innerSL ℝ (x - y)) x := by
    convert (((hsub.norm_sq.const_mul (ε ^ 2)⁻¹).const_sub 1).const_mul 2) using 1
    · funext z
      simp only [div_eq_mul_inv]
      ring
    · ext v
      simp only [smul_apply, neg_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul]
      ring
  have ha := ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)
    (2 * (1 - ‖x - y‖ ^ 2 / ε ^ 2))).hasDerivAt
  simpa only [Function.comp_def, sphereSmoothingKernel, translatedBump, smul_smul] using
    ha.comp_hasFDerivAt x harg

/-- The true radial kernel transfers a rotation derivative between its two
arguments with the exact antisymmetric sign. -/
theorem sphereSmoothingKernel_rotation_antisymmetric {N : ℕ} (ε : ℝ)
    (A : Operator N) (hA : star A = -A) (x y : Vector N) :
    lieDerivative A (fun z => sphereSmoothingKernel ε z y) x =
      -lieDerivative A (sphereSmoothingKernel ε x) y := by
  let d := deriv Real.smoothTransition (2 * (1 - ‖x - y‖ ^ 2 / ε ^ 2))
  have ha : HasDerivAt Real.smoothTransition d (2 * (1 - ‖x - y‖ ^ 2 / ε ^ 2)) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) _).hasDerivAt
  have hl : HasFDerivAt (fun z : Vector N => sphereSmoothingKernel ε z y)
      ((d * (-4 / ε ^ 2)) • innerSL ℝ (x - y)) x := sphereSmoothingKernel_hasFDerivAt_formula ε x y
  have hr : HasFDerivAt (fun z : Vector N => sphereSmoothingKernel ε z x)
      ((d * (-4 / ε ^ 2)) • innerSL ℝ (y - x)) y := by
    simpa only [d, norm_sub_rev] using sphereSmoothingKernel_hasFDerivAt_formula ε y x
  have he : sphereSmoothingKernel ε x = fun z => sphereSmoothingKernel ε z x := by
    funext z
    exact sphereSmoothingKernel_symm ε x z
  rw [he]
  unfold lieDerivative
  rw [hl.fderiv, hr.fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  have hz := skew_inner_self_zero A hA (x - y)
  rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right] at hz
  have hx := skew_inner_self_zero A hA x
  have hy := skew_inner_self_zero A hA y
  simp only [hx, hy, zero_sub, sub_zero] at hz
  rw [inner_sub_left, inner_sub_left, hx, hy]
  have hcross : inner ℝ y (A x) = -inner ℝ x (A y) := by linarith
  rw [hcross]
  ring

lemma sphereSmoothingMoment_derivative_integrable {N : ℕ} {μ : Measure (Vector N)}
    {w : Vector N → ℝ} (hw : Integrable w μ) {ε : ℝ} (hε : 0 < ε) (x : Vector N) :
    Integrable (fun y => w y • fderiv ℝ (sphereRadialBump ε) (x - y)) μ := by
  obtain ⟨B, hB, hb⟩ := sphereRadialBump_derivative_bound (N := N) hε
  have hc := (sphereRadialBump_contDiff (N := N) ε).continuous_fderiv (by simp)
  apply (hw.norm.const_mul B).mono'
    (hw.aestronglyMeasurable.smul ((hc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable))
  exact ae_of_all _ (fun y => by
    change ‖w y • fderiv ℝ (sphereRadialBump ε) (x - y)‖ ≤ B * ‖w y‖
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _)).trans_eq (mul_comm _ _))

/-- Actual smoothing of every genuine zero-energy graph element is a
constant on the actual sphere. This is proved from the completed weighted
integration by parts, the actual kernel, and true smooth rigidity. -/
theorem zero_energy_smoothed_constant {N : ℕ} (hN : 2 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : ContDiff ℝ 1 H)
    (u : sphericalSobolevGraph (show 1 ≤ N by omega) β H hH.continuous)
    (hE : sphericalCompletedDirichlet (show 1 ≤ N by omega) β H hH.continuous u u = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, ∀ x, OnSphere x →
      sphereSmoothingMoment (gibbsLaw N β H) ε
        (gibbsUnweightedDensity β H (sphericalEnergyL2Map (show 1 ≤ N by omega) β H hH.continuous u)) x = c := by
  let f := sphericalEnergyL2Map (show 1 ≤ N by omega) β H hH.continuous u
  let w := gibbsUnweightedDensity β H f
  have hw : Integrable w (gibbsLaw N β H) := gibbsUnweightedDensity_integrable (show 1 ≤ N by omega) β H hH.continuous f
  have hF := sphereSmoothingMoment_contDiff_one hw hε
  apply surfaceGradient_zero_implies_constant hN hF
  intro x hx
  have hrot (i j : Fin N) : lieDerivative (coordinateRotation i j)
      (sphereSmoothingMoment (gibbsLaw N β H) ε w) x = 0 := by
    have hp : ContDiff ℝ 1 (sphereSmoothingKernel ε x) :=
      (sphereSmoothingKernel_right_contDiff ε x).of_le (by simp)
    have hz := zero_energy_annihilates_unweighted_rotation (show 1 ≤ N by omega) β hH hp (i, j) u hE
    have hm := gibbsUnweightedDensity_moment (show 1 ≤ N by omega) β H hH.continuous f
      (lieDerivative (coordinateRotation i j) (sphereSmoothingKernel ε x))
      (lieDerivative_continuous (coordinateRotation i j) hp)
    have hz' : (∫ y, w y * lieDerivative (coordinateRotation i j) (sphereSmoothingKernel ε x) y
      ∂gibbsLaw N β H) = 0 := hm.trans hz
    unfold lieDerivative
    rw [sphereSmoothingMoment_fderiv hw hε,
      ContinuousLinearMap.integral_apply (sphereSmoothingMoment_derivative_integrable hw hε x)]
    calc
      _ = ∫ y, w y * lieDerivative (coordinateRotation i j) (fun z => sphereSmoothingKernel ε z y) x ∂gibbsLaw N β H := by
        apply integral_congr_ae
        apply ae_of_all
        intro y
        simp only [smul_apply, smul_eq_mul, lieDerivative,
          (sphereSmoothingKernel_hasFDerivAt_left ε x y).fderiv]
      _ = -(∫ y, w y * lieDerivative (coordinateRotation i j) (sphereSmoothingKernel ε x) y ∂gibbsLaw N β H) := by
        simp_rw [sphereSmoothingKernel_rotation_antisymmetric ε _ (coordinateRotation_skew i j), mul_neg, integral_neg]
      _ = 0 := by rw [hz', neg_zero]
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [surfaceGradient_rotation_pairing (by omega) _ _ x hx]
  simp only [hrot, zero_mul, Finset.sum_const_zero, mul_zero]

end
end SlowEquilibration.SphericalForm
