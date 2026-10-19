-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourceGaussianLaplaceRatio
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! The Gaussian window fraction in the pure cap Laplace proposition is
positive, at most one, and exhausts Gaussian mass as the width grows. -/
@[expose] public section
namespace SlowEquilibration.SourceGaussianWindowFraction
noncomputable section
open Filter Set MeasureTheory SourceGaussianLaplaceRatio
open scoped Topology
set_option autoImplicit false

private theorem gaussian_integrable {κ : ℝ} (hκ : 0 < κ) :
    Integrable (fun u : ℝ => Real.exp (-κ*u^2/2)) := by
  have heq (u : ℝ) : -κ*u^2/2 = -(κ/2)*u^2 := by ring
  simpa only [heq] using
    (integrable_exp_neg_mul_sq (show 0 < κ/2 by positivity))

/-- A nondegenerate symmetric window has strictly positive Gaussian mass. -/
theorem gaussianWindowFraction_pos {κ w : ℝ} (hκ : 0 < κ) (hw : 0 < w) :
    0 < gaussianWindowFraction κ w := by
  have hwin : 0 < ∫ u in Icc (-w) w, Real.exp (-κ*u^2/2) := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show -w ≤ w by linarith)]
    apply intervalIntegral.integral_pos (show -w < w by linarith)
    · fun_prop
    · intro u hu
      positivity
    · refine ⟨0,⟨by linarith,by linarith⟩,?_⟩
      positivity
  unfold gaussianWindowFraction
  exact div_pos hwin (by positivity)

/-- A finite symmetric window carries at most all Gaussian mass. -/
theorem gaussianWindowFraction_le_one {κ w : ℝ} (hκ : 0 < κ) :
    gaussianWindowFraction κ w ≤ 1 := by
  have hden : 0 < Real.sqrt (Real.pi/(κ/2)) := by positivity
  have hint : Integrable (fun u : ℝ => Real.exp (-κ*u^2/2)) := gaussian_integrable hκ
  have hle := setIntegral_le_integral (s:=Icc (-w) w) hint
    (ae_of_all _ fun _ => Real.exp_nonneg _)
  have hgauss : (∫ u : ℝ, Real.exp (-κ*u^2/2)) =
      Real.sqrt (Real.pi/(κ/2)) := by
    have heq (u : ℝ) : -κ*u^2/2 = -(κ/2)*u^2 := by ring
    simp_rw [heq]
    exact integral_gaussian (κ/2)
  unfold gaussianWindowFraction
  apply (div_le_iff₀ hden).mpr
  simpa only [one_mul,hgauss] using hle

/-- The exterior Gaussian fraction tends to zero as the microscopic window
widens. -/
theorem gaussianWindowFraction_tendsto_one {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun w : ℝ => gaussianWindowFraction κ w) atTop (𝓝 1) := by
  have hint : Integrable (fun u : ℝ => Real.exp (-κ*u^2/2)) := gaussian_integrable hκ
  have htotal := intervalIntegral_tendsto_integral hint
    tendsto_neg_atTop_atBot (tendsto_id : Tendsto (fun w : ℝ => w) atTop atTop)
  have hset : Tendsto
      (fun w : ℝ => ∫ u in Icc (-w) w, Real.exp (-κ*u^2/2)) atTop
      (𝓝 (Real.sqrt (Real.pi/(κ/2)))) := by
    have heq : ∀ᶠ w : ℝ in atTop,
        (∫ u in Icc (-w) w, Real.exp (-κ*u^2/2)) =
          ∫ u in -w..w, Real.exp (-κ*u^2/2) := by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with w hw
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith : -w ≤ w)]
    have hgauss : (∫ u : ℝ, Real.exp (-κ*u^2/2)) =
        Real.sqrt (Real.pi/(κ/2)) := by
      have heq (u : ℝ) : -κ*u^2/2 = -(κ/2)*u^2 := by ring
      simp_rw [heq]
      exact integral_gaussian (κ/2)
    simpa only [hgauss] using
      htotal.congr' (heq.mono fun _ hw => hw.symm)
  have hden : Real.sqrt (Real.pi/(κ/2)) ≠ 0 := by positivity
  have hdiv := hset.div_const (Real.sqrt (Real.pi/(κ/2)))
  have hlim : Real.sqrt (Real.pi/(κ/2)) /
      Real.sqrt (Real.pi/(κ/2)) = 1 := div_self hden
  simpa only [gaussianWindowFraction,hlim] using hdiv

end
end SlowEquilibration.SourceGaussianWindowFraction
