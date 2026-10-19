-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourceUniformScalarRatio
public import SlowEquilibration.SourceGaussianWindowFraction

/-! The source cap/window/complement ratios and uniform positive window
lower bound follow from two uniform unnormalized Laplace limits. -/
@[expose] public section
namespace SlowEquilibration.SourceGaussianWindowRatioBridge
noncomputable section
open Filter Set SourceUniformScalarRatio
open scoped Topology
set_option autoImplicit false

/-- Uniform Laplace limits for the whole cap and a microscopic window yield
all three normalized ratios in source `pc-laplace`. The denominator is the
same whole-cap mass at centered energy zero. -/
theorem uniform_cap_window_ratios
    {T W : ℕ → ℝ → ℝ} {C d Γ L : ℝ}
    (hC : 0 < C) (hd : 0 ≤ d) (hΓ : 0 ≤ Γ) (hL : 0 ≤ L)
    (hT : TendstoUniformlyOn T
      (fun t => C*Real.exp (d*t)) atTop (Icc (-L) L))
    (hW : TendstoUniformlyOn W
      (fun t => C*Real.exp (d*t)*Γ) atTop (Icc (-L) L)) :
    TendstoUniformlyOn
      (fun n t => T n t/T n 0) (fun t => Real.exp (d*t))
      atTop (Icc (-L) L) ∧
    TendstoUniformlyOn
      (fun n t => W n t/T n 0) (fun t => Real.exp (d*t)*Γ)
      atTop (Icc (-L) L) ∧
    TendstoUniformlyOn
      (fun n t => (T n t-W n t)/T n 0)
      (fun t => Real.exp (d*t)*(1-Γ))
      atTop (Icc (-L) L) := by
  have hzero : (0:ℝ) ∈ Icc (-L) L := ⟨by linarith,by linarith⟩
  have hA : Tendsto (fun n => T n 0) atTop (𝓝 C) := by
    simpa only [mul_zero,Real.exp_zero,mul_one] using hT.tendsto_at hzero
  have hEbound (t : ℝ) (ht : t ∈ Icc (-L) L) :
      Real.exp (d*t) ≤ Real.exp (d*L) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left ht.2 hd
  have hTbound : ∀ t ∈ Icc (-L) L,
      |C*Real.exp (d*t)| ≤ C*Real.exp (d*L) := by
    intro t ht
    rw [abs_of_pos (mul_pos hC (Real.exp_pos _))]
    exact mul_le_mul_of_nonneg_left (hEbound t ht) hC.le
  have hWbound : ∀ t ∈ Icc (-L) L,
      |C*Real.exp (d*t)*Γ| ≤ (C*Real.exp (d*L))*Γ := by
    intro t ht
    rw [abs_of_nonneg (mul_nonneg (mul_pos hC (Real.exp_pos _)).le hΓ)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hEbound t ht) hC.le) hΓ
  have hTr := uniformlyOn_div_scalar hT hA hC.ne'
    (mul_nonneg hC.le (Real.exp_pos _).le) hTbound
  have hWr := uniformlyOn_div_scalar hW hA hC.ne'
    (mul_nonneg (mul_nonneg hC.le (Real.exp_pos _).le) hΓ) hWbound
  have hTr' : TendstoUniformlyOn
      (fun n t => T n t/T n 0) (fun t => Real.exp (d*t))
      atTop (Icc (-L) L) := by
    convert hTr using 1 with t
    field_simp
  have hWr' : TendstoUniformlyOn
      (fun n t => W n t/T n 0) (fun t => Real.exp (d*t)*Γ)
      atTop (Icc (-L) L) := by
    convert hWr using 1
    funext t
    field_simp
  refine ⟨hTr',hWr',?_⟩
  have hdiff := hTr'.sub hWr'
  have hfun (n : ℕ) (t : ℝ) :
      T n t/T n 0-W n t/T n 0 = (T n t-W n t)/T n 0 := by ring
  have hlim (t : ℝ) :
      Real.exp (d*t)-Real.exp (d*t)*Γ = Real.exp (d*t)*(1-Γ) := by ring
  convert hdiff using 1
  · ext n t
    exact (hfun n t).symm
  · ext t
    exact (hlim t).symm

/-- The normalized window has a simultaneous positive lower bound on each
fixed energy window. The explicit constant is half the smallest Gaussian
limit over that window. -/
theorem eventually_window_ratio_lower
    {T W : ℕ → ℝ → ℝ} {C d Γ L : ℝ}
    (hC : 0 < C) (hd : 0 ≤ d) (hΓ : 0 < Γ) (hL : 0 ≤ L)
    (hT : TendstoUniformlyOn T
      (fun t => C*Real.exp (d*t)) atTop (Icc (-L) L))
    (hW : TendstoUniformlyOn W
      (fun t => C*Real.exp (d*t)*Γ) atTop (Icc (-L) L)) :
    ∀ᶠ n : ℕ in atTop, ∀ t ∈ Icc (-L) L,
      Real.exp (-d*L)*Γ/2 ≤ W n t/T n 0 := by
  have hWr := (uniform_cap_window_ratios hC hd hΓ.le hL hT hW).2.1
  apply eventually_uniform_lower_half hWr (by positivity)
  intro t ht
  have htl : -L ≤ t := ht.1
  have hmul : -d*L ≤ d*t := by nlinarith
  have he : Real.exp (-d*L) ≤ Real.exp (d*t) := Real.exp_le_exp.mpr hmul
  exact mul_le_mul_of_nonneg_right he hΓ.le

end
end SlowEquilibration.SourceGaussianWindowRatioBridge
