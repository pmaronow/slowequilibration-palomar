-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.NormalizedRadialMeasure
public import SlowEquilibration.RadialLaplaceBounds

/-! Gaussian concentration of the literal normalized radial measure follows
from sharp lower mass and a pointwise Gaussian envelope for its actual density. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.NormalizedRadialMeasure
open Set MeasureTheory RadialGaussianBounds RadialLaplaceBounds
open scoped ENNReal
set_option maxHeartbeats 300000

theorem law_const_mul {f : ℝ → ℝ} {U : Set ℝ} {c : ℝ} (hc : c ≠ 0) :
    law (fun k => c*f k) U=law f U := by
  unfold law
  rw [integral_const_mul]
  congr 1
  funext k
  congr 1
  exact mul_div_mul_left _ _ hc

theorem gaussian_concentration {f : ℝ → ℝ} {U : Set ℝ} (hU : MeasurableSet U)
    (hf : IntegrableOn f U) (h0 : ∀ k,0 ≤ f k)
    {c C a N m θ : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (ha : 0 < a) (hN : 0 < N)
    (hLower : c*Real.exp (N*θ)/Real.sqrt N ≤ ∫ k in U,f k)
    (hUpper : ∀ k ∈ U,f k ≤ C*Real.exp (N*θ)*gaussian (a*N) m k)
    {t : ℝ} (ht : 0 ≤ t) :
    (law f U).real {k : ℝ | t ≤ |k-m|} ≤
      (C*Real.sqrt (Real.pi/(a/2))/c)*Real.exp (-(a/2)*N*t^2) := by
  have hZ : 0 < ∫ k in U,f k :=
    (div_pos (mul_pos hc (Real.exp_pos _)) (Real.sqrt_pos.mpr hN)).trans_le hLower
  rw [law_real_apply hf h0 hZ (measurableSet_le measurable_const (by fun_prop))]
  apply (div_le_iff₀ hZ).mpr
  have hTail := density_tail_upper hU hf (A := C*Real.exp (N*θ))
    (mul_nonneg hC (Real.exp_pos _).le) (mul_pos ha hN) ht hUpper
  have hScale : Real.sqrt (Real.pi/((a*N)/2))=Real.sqrt (Real.pi/(a/2))/Real.sqrt N := by
    rw [show (a*N)/2=(a/2)*N by ring]
    exact gaussian_dimensional_scale (half_pos ha) hN
  rw [hScale,show -((a*N)/2)*t^2=-(a/2)*N*t^2 by ring] at hTail
  have hConst : 0 ≤ (C*Real.sqrt (Real.pi/(a/2))/c)*Real.exp (-(a/2)*N*t^2) := by positivity
  exact hTail.trans (by
    have hh := mul_le_mul_of_nonneg_left hLower hConst
    convert hh using 1
    field_simp)
end SlowEquilibration.NormalizedRadialMeasure
