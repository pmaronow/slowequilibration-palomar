-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeFeatures
public import SlowEquilibration.GaussianNormMean

@[expose] public section

/-!
# Quantitative spatial regularity of the actual tensor field

The actual coefficient feature map is Lipschitz on the sphere. Its constant
is computed directly from the polynomial covariance. Consequently the
literal tensor Hamiltonian has a spatial Lipschitz constant bounded by its
genuine Euclidean disorder norm, whose second moment is its true dimension.
-/

noncomputable section
namespace SlowEquilibration.SphericalModel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators InnerProductSpace

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def spatialVariance {P : ℕ} (c : Degree P → ℝ) : ℝ :=
  ∑ p, c p*(p.val.val : ℝ)

theorem spatialVariance_nonneg {P : ℕ} (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) :
    0 ≤ spatialVariance c := Finset.sum_nonneg fun p _ => mul_nonneg (hc p) (by positivity)

theorem one_sub_pow_le_mul {r : ℝ} (hr : |r| ≤ 1) (p : ℕ) :
    1-r^p ≤ (p : ℝ)*(1-r) := by
  induction p with
  | zero => simp
  | succ p ih =>
    have hp : r^p ≤ 1 := (le_abs_self _).trans (by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) hr)
    have hm := mul_le_mul_of_nonneg_right hp (show 0 ≤ 1-r by linarith [abs_le.mp hr])
    rw [pow_succ]
    push_cast
    nlinarith

theorem covariancePolynomial_sphere_increment {P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) {r : ℝ} (hr : |r| ≤ 1) :
    covariancePolynomial c 1-covariancePolynomial c r ≤ spatialVariance c*(1-r) := by
  unfold covariancePolynomial spatialVariance
  rw [← Finset.sum_sub_distrib,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p _
  simpa only [one_pow,mul_one,mul_sub,mul_assoc] using
    mul_le_mul_of_nonneg_left (one_sub_pow_le_mul hr p.val.val) (hc p)

/-- Spatial Lipschitz regularity of the genuine Gaussian coefficient map. -/
theorem fieldFeature_dist_le {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p)
    (x y : Vector N) (hx : ‖x‖^2=(N : ℝ)) (hy : ‖y‖^2=(N : ℝ)) :
    ‖fieldFeature c x-fieldFeature c y‖ ≤ Real.sqrt (spatialVariance c)*‖x-y‖ := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hxy : |overlap x y| ≤ 1 := by
    rw [overlap,abs_div,abs_of_pos hNr]
    apply (div_le_one hNr).mpr
    have hh := abs_real_inner_le_norm x y
    have he : ‖x‖*‖y‖=(N : ℝ) := by
      have hnorm : ‖x‖=‖y‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hx.trans hy.symm)
      rw [hnorm,← sq,hy]
    rwa [he] at hh
  have hc' := covariancePolynomial_sphere_increment c hc hxy
  have hmul := mul_le_mul_of_nonneg_left hc' (show 0 ≤ 2*(N : ℝ) by positivity)
  have hnorm : ‖fieldFeature c x-fieldFeature c y‖^2 =
      2*(N : ℝ)*(covariancePolynomial c 1-covariancePolynomial c (overlap x y)) := by
    rw [norm_sub_sq_real,fieldFeature_norm_sq hN c hc x hx,
      fieldFeature_norm_sq hN c hc y hy,fieldFeature_inner_gram hN c hc]
    ring
  have hs : ‖x-y‖^2 = 2*(N : ℝ)*(1-overlap x y) := by
    rw [norm_sub_sq_real,hx,hy,overlap]
    field_simp
    ring
  have hsp := Real.sq_sqrt (spatialVariance_nonneg c hc)
  have hb : ‖fieldFeature c x-fieldFeature c y‖^2 ≤
      (Real.sqrt (spatialVariance c)*‖x-y‖)^2 := by
    rw [mul_pow,hsp,hs,hnorm]
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hb

/-- The true tensor realization is spatially Lipschitz with its actual
coefficient norm; no high-probability regularity event is assumed. -/
theorem field_spatial_dist_le {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (J : Disorder N P)
    (x y : Vector N) (hx : ‖x‖^2=(N : ℝ)) (hy : ‖y‖^2=(N : ℝ)) :
    |field c J x-field c J y| ≤
      ‖euclideanDisorder J‖*Real.sqrt (spatialVariance c)*‖x-y‖ := by
  have he (v : Vector N) : field c J v = inner ℝ (euclideanDisorder J) (fieldFeature c v) := by
    rw [fieldFeature_inner,unpack_euclideanDisorder]
  rw [he x,he y,← inner_sub_right]
  calc
    _ ≤ ‖euclideanDisorder J‖*‖fieldFeature c x-fieldFeature c y‖ := abs_real_inner_le_norm _ _
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (fieldFeature_dist_le hN c hc x y hx hy)
        (norm_nonneg (euclideanDisorder J))
      simpa only [mul_assoc] using hh

/-- The exact second moment of the actual tensor coefficient norm. -/
theorem euclideanDisorder_norm_sq_integral (N P : ℕ) :
    (∫ J : Disorder N P, ‖euclideanDisorder J‖^2 ∂disorderLaw N P) =
      (Fintype.card (Coordinate N P) : ℝ) := by
  have he := (euclideanDisorder_hasLaw N P).integral_comp
    (f := fun g : EuclideanDisorder N P => ‖g‖^2) (by fun_prop)
  dsimp only [Function.comp_apply] at he
  rw [he]
  exact GaussianNormMean.standardGaussian_integral_norm_sq _

end SlowEquilibration.SphericalModel
