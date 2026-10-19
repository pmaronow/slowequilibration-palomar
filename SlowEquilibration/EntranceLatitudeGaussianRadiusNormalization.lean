-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntranceLatitudeGaussianRadius
public import Mathlib.Topology.MetricSpace.Lipschitz

/-! The radial normalization defining the literal spherical law is
uniformly Lipschitz on the Gaussian annulus used for concentration. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.EntranceLatitudeGaussianRadius
open MeasureTheory ProbabilityTheory Set
open SphericalAging.FiniteModel SphericalAging.SphereInitialLaw
open scoped NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Quantitative radial normalization away from zero. -/
theorem radial_normalization_dist_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {r : ℝ} (hr : 0 ≤ r) (x y : E)
    (hx : 0 < ‖x‖) (hy : 0 < ‖y‖) :
    dist ((r / ‖x‖) • x) ((r / ‖y‖) • y) ≤
      (2 * r / ‖x‖) * dist x y := by
  have ha : 0 ≤ r / ‖x‖ := div_nonneg hr hx.le
  have he : (r / ‖x‖) • x - (r / ‖y‖) • y =
      (r / ‖x‖) • (x - y) + (r / ‖x‖ - r / ‖y‖) • y := by
    module
  have hs : (r / ‖x‖ - r / ‖y‖) * ‖y‖ = (r / ‖x‖) * (‖y‖ - ‖x‖) := by
    field_simp
  have habs : |r / ‖x‖ - r / ‖y‖| * ‖y‖ = (r / ‖x‖) * |‖y‖ - ‖x‖| := by
    calc
      _ = |(r / ‖x‖ - r / ‖y‖) * ‖y‖| := by
        rw [abs_mul, abs_of_pos hy]
      _ = _ := by rw [hs, abs_mul, abs_of_nonneg ha]
  rw [dist_eq_norm, he]
  calc
    _ ≤ ‖(r / ‖x‖) • (x - y)‖ + ‖(r / ‖x‖ - r / ‖y‖) • y‖ := norm_add_le _ _
    _ = (r / ‖x‖) * ‖x - y‖ + (r / ‖x‖) * |‖y‖ - ‖x‖| := by
      rw [norm_smul, Real.norm_of_nonneg ha, norm_smul, Real.norm_eq_abs, habs]
    _ ≤ (r / ‖x‖) * ‖x - y‖ + (r / ‖x‖) * ‖x - y‖ := by
      gcongr
      simpa [norm_sub_rev] using abs_norm_sub_norm_le y x
    _ = _ := by rw [dist_eq_norm]; ring

/-- The physical normalization has Lipschitz constant four on the annulus
`norm >= sqrt N / 2`, independently of N. -/
theorem normalize_lipschitzOn_annulus {N : ℕ} (hN : 0 < N) :
    LipschitzOnWith 4 (normalize N)
      {x : Vector N | Real.sqrt (N : ℝ) / 2 ≤ ‖x‖} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  change Real.sqrt (N : ℝ) / 2 ≤ ‖x‖ at hx
  change Real.sqrt (N : ℝ) / 2 ≤ ‖y‖ at hy
  have hr : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hx0 : 0 < ‖x‖ := by linarith
  have hy0 : 0 < ‖y‖ := by linarith
  have ha : 2 * Real.sqrt (N : ℝ) / ‖x‖ ≤ 4 := by
    apply (div_le_iff₀ hx0).mpr
    linarith
  exact (radial_normalization_dist_le hr.le x y hx0 hy0).trans
    (mul_le_mul_of_nonneg_right ha dist_nonneg)

/-- Composing any Lipschitz observable on the actual sphere with radial
normalization admits a genuine global Gaussian Lipschitz extension. -/
theorem sphere_observable_gaussian_extension {N : ℕ} (hN : 0 < N)
    (f : Vector N → ℝ) (L : ℝ≥0)
    (hf : LipschitzOnWith L f {x | ‖x‖ = Real.sqrt (N : ℝ)}) :
    ∃ g : Vector N → ℝ, LipschitzWith (4 * L) g ∧
      EqOn (f ∘ normalize N) g {x | Real.sqrt (N : ℝ) / 2 ≤ ‖x‖} := by
  apply LipschitzOnWith.extend_real
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  change Real.sqrt (N : ℝ) / 2 ≤ ‖x‖ at hx
  change Real.sqrt (N : ℝ) / 2 ≤ ‖y‖ at hy
  have hr : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hx0 : x ≠ 0 := by intro he; subst x; simp only [norm_zero] at hx; linarith
  have hy0 : y ≠ 0 := by intro he; subst y; simp only [norm_zero] at hy; linarith
  have hb := hf.dist_le_mul (normalize N x) (normalize_norm x hx0)
    (normalize N y) (normalize_norm y hy0)
  have hn := (normalize_lipschitzOn_annulus hN).dist_le_mul x hx y hy
  apply hb.trans
  simpa only [NNReal.coe_mul, NNReal.coe_ofNat, mul_assoc, mul_left_comm] using
    mul_le_mul_of_nonneg_left hn L.coe_nonneg

end SlowEquilibration.EntranceLatitudeGaussianRadius
