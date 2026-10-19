-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SpherePolarIntegral
public import SlowEquilibration.GaussianShell

/-! Finite-dimensional fractional Gaussian moments of the genuine spherical
linear partition function, using a shell of actual Gaussian radial mass. -/

@[expose] public section
namespace SlowEquilibration.SphereLinear
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphereVolume
open scoped RealInnerProductSpace ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem log_partition_shell_upper {z R U : ℝ} (hz : 1 ≤ z) (hR : 0 ≤ R) (hRU : R ≤ U)
    (hmass : (1 / 2 : ℝ) ≤ (gaussianRadius E).real
      {r : Ioi (0 : ℝ) | R ≤ (r : ℝ) ∧ (r : ℝ) ≤ U}) (w : E) :
    Real.log (partition w R) ≤ Real.log 2 + (z - 1) / 2 * U ^ 2 -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log z + ‖w‖ ^ 2 / (2 * z) := by
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  let B := -(z - 1) / 2 * U ^ 2
  have hb := shell_partition_bound hz hR hRU w
  have h := (mul_le_mul_of_nonneg_right hmass
    (mul_nonneg (Real.exp_pos B).le (partition_pos w R).le)).trans hb
  have hden : 0 < (1 / 2 : ℝ) * Real.exp B := by positivity
  have hd : partition w R ≤
      (z ^ (-((Module.finrank ℝ E : ℝ) / 2)) * Real.exp (‖w‖ ^ 2 / (2 * z))) /
        ((1 / 2 : ℝ) * Real.exp B) := by
    apply (le_div_iff₀ hden).mpr
    convert h using 1 <;> ring
  have hl := Real.log_le_log (partition_pos w R) hd
  rw [Real.log_div (mul_ne_zero (Real.rpow_pos_of_pos hz0 _).ne' (Real.exp_ne_zero _)) hden.ne',
    Real.log_mul (Real.rpow_pos_of_pos hz0 _).ne' (Real.exp_ne_zero _),
    Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0) (Real.exp_ne_zero _),
    Real.log_exp, Real.log_exp, Real.log_rpow hz0,
    show Real.log (1 / 2 : ℝ) = -Real.log 2 by rw [one_div, Real.log_inv]] at hl
  dsimp [B] at hl
  linarith

theorem fractional_moment_shell_upper {z R U a c : ℝ} (hz : 1 ≤ z)
    (hR : 0 ≤ R) (hRU : R ≤ U) (ha : 0 ≤ a) (hac : a * c ^ 2 < z)
    (hmass : (1 / 2 : ℝ) ≤ (gaussianRadius E).real
      {r : Ioi (0 : ℝ) | R ≤ (r : ℝ) ∧ (r : ℝ) ≤ U}) :
    (∫ g : E, Real.exp (a * Real.log (partition (c • g) R)) ∂stdGaussian E) ≤
      Real.exp (a * (Real.log 2 + (z - 1) / 2 * U ^ 2 -
        (Module.finrank ℝ E : ℝ) / 2 * Real.log z) -
          (Module.finrank ℝ E : ℝ) / 2 * Real.log (1 - a * c ^ 2 / z)) := by
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  let K := Real.log 2 + (z - 1) / 2 * U ^ 2 -
    (Module.finrank ℝ E : ℝ) / 2 * Real.log z
  let t := a * c ^ 2 / (2 * z)
  have ht : t < 1 / 2 := by
    apply (div_lt_iff₀ (by positivity : 0 < 2 * z)).mpr
    nlinarith
  have hbound (g : E) :
      Real.exp (a * Real.log (partition (c • g) R)) ≤
        Real.exp (a * K) * Real.exp (t * ‖g‖ ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left (log_partition_shell_upper hz hR hRU hmass (c • g)) ha
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
    dsimp [K, t]
    convert h using 1 <;> ring
  have hi := (GaussianShell.integrable_exp_norm_sq (E := E) ht).const_mul (Real.exp (a * K))
  calc
    _ ≤ ∫ g : E, Real.exp (a * K) * Real.exp (t * ‖g‖ ^ 2) ∂stdGaussian E :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
        hi (Filter.Eventually.of_forall hbound)
    _ = _ := by
      rw [integral_const_mul, GaussianShell.integral_exp_norm_sq ht,
        Real.rpow_def_of_pos (by linarith : 0 < 1 - 2 * t), ← Real.exp_add]
      congr 1
      have he : 1 - 2 * t = 1 - a * c ^ 2 / z := by dsimp [t]; ring
      rw [he]
      dsimp [K]
      ring

end
end SlowEquilibration.SphereLinear
