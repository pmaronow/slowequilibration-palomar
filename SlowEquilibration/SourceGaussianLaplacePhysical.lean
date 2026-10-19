-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourceGaussianLaplaceLocal
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Change of variables from the physical latitude to microscopic coordinates. -/
@[expose] public section
namespace SlowEquilibration.SourceGaussianLaplacePhysical
noncomputable section
open Filter Set MeasureTheory SourceGaussianLaplaceScaled
open scoped Topology

/-- Exact identity between the local latitude integral and the scaled kernel. -/
theorem scaledKernel_integral_eq_physical (φ a : ℝ → ℝ) (m l r : ℝ)
    (hlr : l ≤ r) (n : ℕ) :
    (∫ u, scaledKernel φ a m l r n u) =
      Real.sqrt (n+2 : ℕ) *
        (∫ t in l..r, a t*Real.exp ((n+2 : ℕ)*(φ t-φ m))) := by
  let s : ℝ := Real.sqrt (n+2 : ℕ)
  let L : ℝ := s*(l-m)
  let R : ℝ := s*(r-m)
  let f : ℝ → ℝ := fun t => a t*Real.exp ((n+2 : ℕ)*(φ t-φ m))
  have hs : 0 < s := by dsimp [s]; positivity
  have hs0 : s ≠ 0 := hs.ne'
  have hLR : L ≤ R := by dsimp [L,R]; exact mul_le_mul_of_nonneg_left (sub_le_sub_right hlr m) hs.le
  have hL : m+L/s = l := by
    dsimp [L]
    field_simp
    ring
  have hR : m+R/s = r := by
    dsimp [R]
    field_simp
    ring
  have hchange :
      (∫ u in L..R, f (m+u/s)) = s*(∫ t in l..r, f t) := by
    rw [intervalIntegral.integral_comp_add_div (f:=f) hs0 m]
    rw [hL,hR]
    simp only [smul_eq_mul]
  have hkernel : scaledKernel φ a m l r n =
      (Icc L R).indicator (fun u => f (m+u/s)) := by
    funext u
    simp [scaledKernel, Set.indicator, f, L, R, s]
  calc
    (∫ u, scaledKernel φ a m l r n u)
        = ∫ u in Icc L R, f (m+u/s) := by
          rw [hkernel]
          rw [integral_indicator measurableSet_Icc]
    _ = ∫ u in L..R, f (m+u/s) := by
          rw [intervalIntegral.integral_of_le hLR, ← integral_Icc_eq_integral_Ioc]
    _ = s*(∫ t in l..r, f t) := hchange
    _ = _ := rfl

/-- The physical local integral has the exact Gaussian prefactor. -/
theorem physical_local_gaussian {φ a : ℝ → ℝ} {m l r κ c M : ℝ}
    (hφ : ContDiffOn ℝ 2 φ (Ioo l r)) (hφmeas : Measurable φ)
    (ha : ContinuousOn a (Icc l r)) (hameas : Measurable a)
    (hstat : derivWithin φ (Ioo l r) m = 0)
    (hcurv : iteratedDerivWithin 2 φ (Ioo l r) m = -κ)
    (hl : l < m) (hr : m < r)
    (hc : 0 < c) (hM : 0 ≤ M)
    (hamp : ∀ t ∈ Icc l r, |a t| ≤ M)
    (henv : ∀ t ∈ Icc l r, φ t ≤ φ m-c*(t-m)^2) :
    Tendsto (fun n : ℕ => Real.sqrt (n+2 : ℕ) *
      (∫ t in l..r, a t*Real.exp ((n+2 : ℕ)*(φ t-φ m)))) atTop
      (𝓝 (a m*Real.sqrt (Real.pi/(κ/2)))) := by
  have h := SourceGaussianLaplaceLocal.integral_scaledKernel_gaussian_local
    hφ hφmeas ha hameas hstat hcurv hl hr hc hM hamp henv
  exact h.congr' (.of_forall fun n => scaledKernel_integral_eq_physical φ a m l r
    (hl.le.trans hr.le) n)

end
end SlowEquilibration.SourceGaussianLaplacePhysical
