-- SPDX-License-Identifier: Apache-2.0
module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Uniform control of scalar shifts in fixed logarithmic windows. -/
@[expose] public section
namespace SlowEquilibration.NatLogWindowScales
noncomputable section
open Set Filter
open scoped Topology
set_option maxHeartbeats 200000

theorem log_power_div_dimension_tendsto_zero (p : ℕ) :
    Tendsto (fun n : ℕ => (Real.log (n+2 : ℕ))^p/(n+2 : ℕ)) atTop (𝓝 (0 : ℝ)) := by
  simpa only [one_mul,add_zero,Function.comp_def] using
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 p one_ne_zero).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))

theorem inverse_sqrt_dimension_tendsto_zero :
    Tendsto (fun n : ℕ => 1/Real.sqrt (n+2 : ℕ)) atTop (𝓝 (0 : ℝ)) := by
  simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)))

theorem uniform_log_window_eventually {D b u : ℝ} (hD : 0 ≤ D) (hb : 0 < b) (hu : 0 < u)
    (B : ℝ) : ∀ᶠ n : ℕ in atTop,∀ σ : ℝ,|σ| ≤ D*Real.log (n+2 : ℕ) →
      σ^2/(n+2 : ℕ) ≤ 1 ∧
      |B*σ/(2*b*(n+2 : ℕ))|+1/Real.sqrt (n+2 : ℕ) < u := by
  have hq : Tendsto (fun n : ℕ => D^2*(Real.log (n+2 : ℕ))^2/(n+2 : ℕ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_div_assoc,mul_zero] using (log_power_div_dimension_tendsto_zero 2).const_mul (D^2)
  have hs : Tendsto (fun n : ℕ => (|B| * D/(2*b))*(Real.log (n+2 : ℕ)/(n+2 : ℕ))+
      1/Real.sqrt (n+2 : ℕ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [pow_one,mul_zero,zero_add] using
      ((log_power_div_dimension_tendsto_zero 1).const_mul (|B| * D/(2*b))).add
        inverse_sqrt_dimension_tendsto_zero
  filter_upwards [hq.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hs.eventually (gt_mem_nhds hu)] with n hnq hns
  intro σ hσ
  have hN : 0 < ((n+2 : ℕ) : ℝ) := by positivity
  have hlog : 0 ≤ Real.log (n+2 : ℕ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ n+2 by omega))
  have hsq := (sq_le_sq₀ (abs_nonneg σ) (mul_nonneg hD hlog)).mpr hσ
  rw [sq_abs,mul_pow] at hsq
  constructor
  · exact (div_le_div_of_nonneg_right hsq hN.le).trans hnq.le
  · have hshift : |B*σ/(2*b*(n+2 : ℕ))| ≤
        (|B| * D/(2*b))*(Real.log (n+2 : ℕ)/(n+2 : ℕ)) := by
      rw [abs_div,abs_mul,abs_of_pos (by positivity : 0 < 2*b*(n+2 : ℕ))]
      apply le_trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hσ (abs_nonneg B)) (by positivity))
      apply le_of_eq
      field_simp
    have htotal : |B*σ/(2*b*(n+2 : ℕ))|+1/Real.sqrt (n+2 : ℕ) ≤
        (|B| * D/(2*b))*(Real.log (n+2 : ℕ)/(n+2 : ℕ))+1/Real.sqrt (n+2 : ℕ) := by linarith
    exact htotal.trans_lt hns

end
end SlowEquilibration.NatLogWindowScales
