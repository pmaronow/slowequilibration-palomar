-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.NatLogWindowScales

@[expose] public section
noncomputable section
namespace SlowEquilibration.NatLogWindowScales
open Set Filter
open scoped Topology

theorem log_bounded_sequence_div_dimension_tendsto_zero {D : ℝ} (_hD : 0 ≤ D)
    (σ : ℕ → ℝ) (hσ : ∀ᶠ n : ℕ in atTop,|σ n| ≤ D*Real.log (n+2 : ℕ)) :
    Tendsto (fun n : ℕ => σ n/(n+2 : ℕ)) atTop (𝓝 (0 : ℝ)) := by
  have ht : Tendsto (fun n : ℕ => D*Real.log (n+2 : ℕ)/(n+2 : ℕ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [pow_one,mul_zero,mul_div_assoc] using (log_power_div_dimension_tendsto_zero 1).const_mul D
  apply squeeze_zero_norm' _ ht
  filter_upwards [hσ] with n hn
  rw [Real.norm_eq_abs,abs_div,abs_of_pos (by positivity : 0 < ((n+2 : ℕ) : ℝ))]
  exact div_le_div_of_nonneg_right hn (by positivity)

theorem normalized_center_log_bounded {E₀ c₀ M : ℝ} (hc₀ : 0 < c₀) (hM : 0 ≤ M)
    (m : ℕ → ℝ)
    (hcenter : ∀ᶠ n : ℕ in atTop,|m n-((n+2 : ℕ)*E₀-Real.log (n+2 : ℕ)/(2*c₀))| ≤ M) :
    ∀ᶠ n : ℕ in atTop,|m n-(n+2 : ℕ)*E₀| ≤ (1/(2*c₀)+1)*Real.log (n+2 : ℕ) := by
  have hlogTop : Tendsto (fun n : ℕ => Real.log (n+2 : ℕ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
  filter_upwards [hcenter,hlogTop.eventually (eventually_ge_atTop M)] with n hn hlogM
  have hlog : 0 ≤ Real.log (n+2 : ℕ) := hM.trans hlogM
  have he : ((n+2 : ℕ)*E₀-Real.log (n+2 : ℕ)/(2*c₀))-(n+2 : ℕ)*E₀=
      -(Real.log (n+2 : ℕ)/(2*c₀)) := by ring
  have htriangle := abs_sub_le (m n) ((n+2 : ℕ)*E₀-Real.log (n+2 : ℕ)/(2*c₀)) ((n+2 : ℕ)*E₀)
  rw [he,abs_neg,abs_of_nonneg (by positivity : 0 ≤ Real.log (n+2 : ℕ)/(2*c₀))] at htriangle
  calc
    _ ≤ M+Real.log (n+2 : ℕ)/(2*c₀) := htriangle.trans (by linarith)
    _ ≤ Real.log (n+2 : ℕ)+Real.log (n+2 : ℕ)/(2*c₀) := by linarith
    _=_ := by ring

end SlowEquilibration.NatLogWindowScales
