-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourceGaussianLaplaceTaylor
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The manuscript's logarithmic centering perturbation disappears on the
microscopic latitude scale, even though `log N` diverges. -/
@[expose] public section
namespace SlowEquilibration.SourcePureLogPolynomialTangent
noncomputable section
open Filter Set
open scoped Topology

/-- The logarithm is negligible compared with the square-root width. -/
theorem log_div_sqrt_dimension_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (n+2 : ℕ)/Real.sqrt (n+2 : ℕ))
      atTop (𝓝 (0 : ℝ)) := by
  have h := (isLittleO_log_rpow_rpow_atTop 1
    (show (0:ℝ)<1/2 by norm_num)).tendsto_div_nhds_zero
  have hn := h.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
  simpa only [Function.comp_def, Real.rpow_one, Real.sqrt_eq_rpow] using hn

/-- Powers are `p`-Lipschitz on the physical latitude range `[-1,1]`. -/
theorem power_lipschitz_unit (p : ℕ) {z m : ℝ}
    (hz : |z| ≤ 1) (hm : |m| ≤ 1) :
    |z^p-m^p| ≤ (p:ℝ)*|z-m| := by
  have hpow : max |z| |m| ^ (p-1) ≤ 1 := by
    have hmax : max |z| |m| ≤ (1:ℝ) := max_le hz hm
    calc
      _ ≤ (1:ℝ)^(p-1) := by gcongr
      _ = 1 := by simp
  calc
    _ ≤ |z-m| * (p:ℝ)*max |z| |m|^(p-1) := abs_pow_sub_pow_le z m p
    _ ≤ |z-m| * (p:ℝ)*1 := by gcongr
    _ = _ := by ring

/-- The exact source term `log N (a^p-q^p)` vanishes for
`a=q+u/√N` and fixed microscopic displacement `u`. -/
theorem log_power_gap_tendsto_zero (p : ℕ) {m : ℝ}
    (hm : m ∈ Ioo (-1:ℝ) 1) (u : ℝ) :
    Tendsto (fun n : ℕ => Real.log (n+2 : ℕ)*
      ((m+u/Real.sqrt (n+2 : ℕ))^p-m^p)) atTop (𝓝 (0 : ℝ)) := by
  let z : ℕ → ℝ := fun n => m+u/Real.sqrt (n+2 : ℕ)
  have hz : Tendsto z atTop (𝓝 m) := SourceGaussianLaplaceTaylor.scaled_tendsto m u
  have hmabs : |m| ≤ 1 := (abs_lt.mpr hm).le
  have hmem : ∀ᶠ n : ℕ in atTop, |z n| ≤ 1 := by
    filter_upwards [hz.eventually (Ioo_mem_nhds hm.1 hm.2)] with n hn
    exact (abs_lt.mpr hn).le
  have hbound : ∀ᶠ n : ℕ in atTop,
      ‖Real.log (n+2 : ℕ)*(z n^p-m^p)‖ ≤
        ((p:ℝ)*|u|)*(Real.log (n+2 : ℕ)/Real.sqrt (n+2 : ℕ)) := by
    filter_upwards [hmem] with n hn
    have hs : 0 < Real.sqrt (n+2 : ℕ) := by positivity
    have hlog : 0 ≤ Real.log (n+2 : ℕ) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ n+2 by omega))
    have hgap := power_lipschitz_unit p hn hmabs
    have hdist : |z n-m| = |u|/Real.sqrt (n+2 : ℕ) := by
      dsimp [z]
      rw [add_sub_cancel_left, abs_div, abs_of_pos hs]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hlog]
    calc
      _ ≤ Real.log (n+2 : ℕ)*((p:ℝ)*|z n-m|) :=
        mul_le_mul_of_nonneg_left hgap hlog
      _ = ((p:ℝ)*|u|)*(Real.log (n+2 : ℕ)/Real.sqrt (n+2 : ℕ)) := by
        rw [hdist]
        ring
  apply squeeze_zero_norm' hbound
  simpa only [mul_zero] using
    log_div_sqrt_dimension_tendsto_zero.const_mul ((p:ℝ)*|u|)

/-- The source's full `β(t−log N/(2c_p))(a^p-q^p)` term vanishes at
fixed `t` and fixed microscopic displacement. -/
theorem centered_log_polynomial_tendsto_zero (p : ℕ) {m : ℝ}
    (hm : m ∈ Ioo (-1:ℝ) 1) (β t cp u : ℝ) :
    Tendsto (fun n : ℕ => β*(t-Real.log (n+2 : ℕ)/(2*cp))*
      ((m+u/Real.sqrt (n+2 : ℕ))^p-m^p))
      atTop (𝓝 (0 : ℝ)) := by
  have hz := SourceGaussianLaplaceTaylor.scaled_tendsto m u
  have hpow : Tendsto (fun n : ℕ =>
      ((m+u/Real.sqrt (n+2 : ℕ))^p-m^p)) atTop (𝓝 0) := by
    simpa only [sub_self] using (hz.pow p).sub_const (m^p)
  have hlog := log_power_gap_tendsto_zero p hm u
  have htotal := ((hpow.const_mul t).sub
    (hlog.const_mul (1/(2*cp)))).const_mul β
  convert htotal using 1
  · funext n
    ring
  · ring

end
end SlowEquilibration.SourcePureLogPolynomialTangent
