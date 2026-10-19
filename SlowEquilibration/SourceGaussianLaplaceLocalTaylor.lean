-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourceGaussianLaplaceTaylor

/-! Microscopic Taylor expansion using smoothness only on an open saddle neighborhood. -/
@[expose] public section
namespace SlowEquilibration.SourceGaussianLaplaceLocalTaylor
noncomputable section
open Filter Set
open scoped Topology

private theorem local_taylor_poly_two {φ : ℝ → ℝ} {l m r q : ℝ}
    (hstat : derivWithin φ (Ioo l r) m = 0)
    (hcurv : iteratedDerivWithin 2 φ (Ioo l r) m = q) (x : ℝ) :
    taylorWithinEval φ 2 (Ioo l r) m x = φ m + q/2*(x-m)^2 := by
  have h1 : iteratedDerivWithin 1 φ (Ioo l r) m = 0 := by
    simpa [iteratedDerivWithin_succ] using hstat
  simp [show (2:ℕ)=1+1 by omega, taylorWithinEval_succ, h1, hcurv]
  ring

/-- A local C² stationary exponent has the expected Gaussian tangent at the
`u/√(n+2)` scale. No smooth extension across the endpoints is required. -/
theorem scaled_quadratic_tangent_local {φ : ℝ → ℝ} {l m r q : ℝ}
    (hl : l < m) (hr : m < r)
    (hφ : ContDiffOn ℝ 2 φ (Ioo l r))
    (hstat : derivWithin φ (Ioo l r) m = 0)
    (hcurv : iteratedDerivWithin 2 φ (Ioo l r) m = q) (u : ℝ) :
    Tendsto (fun n : ℕ => (n+2 : ℕ) *
      (φ (m+u/Real.sqrt (n+2 : ℕ))-φ m)) atTop (𝓝 (q*u^2/2)) := by
  let z : ℕ → ℝ := fun n => m+u/Real.sqrt (n+2 : ℕ)
  have hz : Tendsto z atTop (𝓝 m) := SourceGaussianLaplaceTaylor.scaled_tendsto m u
  have ht : Tendsto (fun n : ℕ =>
      (φ (z n)-taylorWithinEval φ 2 (Ioo l r) m (z n))/(z n-m)^2)
      atTop (𝓝 0) := by
    have hTaylor : Tendsto
        (fun x => (φ x-taylorWithinEval φ 2 (Ioo l r) m x)/(x-m)^2)
        (𝓝 m) (𝓝 0) := by
      simpa only [nhdsWithin_eq_nhds.mpr (Ioo_mem_nhds hl hr)] using
        Real.taylor_tendsto (convex_Ioo l r) (show m ∈ Ioo l r from ⟨hl,hr⟩) hφ
    exact hTaylor.comp hz
  have hzero : Tendsto (fun n : ℕ => u^2 *
      ((φ (z n)-taylorWithinEval φ 2 (Ioo l r) m (z n))/(z n-m)^2))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using ht.const_mul (u^2)
  have heq (n : ℕ) :
      u^2 * ((φ (z n)-taylorWithinEval φ 2 (Ioo l r) m (z n))/(z n-m)^2) =
      (n+2 : ℕ) * (φ (z n)-φ m)-q*u^2/2 := by
    have hs : Real.sqrt (n+2 : ℕ) ≠ 0 := by positivity
    by_cases hu : u=0
    · subst u; simp [z]
    · have hz0 : z n-m ≠ 0 := by
        dsimp [z]; rw [add_sub_cancel_left]; exact div_ne_zero hu hs
      have hscale : u^2 = ((n+2 : ℕ) : ℝ)*(z n-m)^2 := by
        dsimp [z]
        rw [add_sub_cancel_left, div_pow,
          Real.sq_sqrt (show 0 ≤ ((n+2 : ℕ) : ℝ) by positivity)]
        field_simp
      calc
        _ = ((n+2 : ℕ) : ℝ)*(φ (z n)-taylorWithinEval φ 2 (Ioo l r) m (z n)) := by
          rw [hscale]
          field_simp [hz0]
        _ = ((n+2 : ℕ) : ℝ)*(φ (z n)-φ m)-q*u^2/2 := by
          rw [local_taylor_poly_two hstat hcurv, hscale]
          ring
  convert hzero.add_const (q*u^2/2) using 1
  · funext n; rw [heq]; ring
  · ring

end
end SlowEquilibration.SourceGaussianLaplaceLocalTaylor
