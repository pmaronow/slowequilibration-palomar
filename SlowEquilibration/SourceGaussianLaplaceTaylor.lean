-- SPDX-License-Identifier: Apache-2.0
module
public import Mathlib.Analysis.Calculus.Taylor
public import SlowEquilibration.NatLogWindowScales

/-! Quadratic Taylor asymptotics on the microscopic scale. -/
@[expose] public section
namespace SlowEquilibration.SourceGaussianLaplaceTaylor
noncomputable section
open Filter Set
open scoped Topology

private theorem sqrt_dim_pos (n : ℕ) : 0 < Real.sqrt (n+2 : ℕ) := by positivity

theorem scaled_tendsto (m u : ℝ) :
    Tendsto (fun n : ℕ => m + u / Real.sqrt (n+2 : ℕ)) atTop (𝓝 m) := by
  simpa [div_eq_mul_inv] using
    tendsto_const_nhds.add ((NatLogWindowScales.inverse_sqrt_dimension_tendsto_zero).const_mul u)

private theorem taylor_poly_two {φ : ℝ → ℝ} {m q : ℝ}
    (hstat : deriv φ m = 0) (hcurv : iteratedDeriv 2 φ m = q) (x : ℝ) :
    taylorWithinEval φ 2 univ m x = φ m + q / 2 * (x-m)^2 := by
  have h1 : iteratedDerivWithin 1 φ univ m = 0 := by
    simpa [iteratedDerivWithin_succ, derivWithin_univ] using hstat
  have h2 : iteratedDerivWithin 2 φ univ m = q := by
    simpa only [iteratedDerivWithin_univ] using hcurv
  simp [show (2:ℕ)=1+1 by omega, taylorWithinEval_succ, h1, h2]
  ring

theorem scaled_quadratic_tangent {φ : ℝ → ℝ} {m q : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hstat : deriv φ m = 0)
    (hcurv : iteratedDeriv 2 φ m = q) (u : ℝ) :
    Tendsto (fun n : ℕ => (n+2 : ℕ) *
      (φ (m + u / Real.sqrt (n+2 : ℕ)) - φ m)) atTop (𝓝 (q*u^2/2)) := by
  let z : ℕ → ℝ := fun n => m + u / Real.sqrt (n+2 : ℕ)
  have hz : Tendsto z atTop (𝓝 m) := scaled_tendsto m u
  have ht : Tendsto (fun n : ℕ =>
      (φ (z n) - taylorWithinEval φ 2 univ m (z n)) / (z n - m)^2)
      atTop (𝓝 0) := by
    have hTaylor : Tendsto
        (fun x => (φ x - taylorWithinEval φ 2 univ m x) / (x-m)^2)
        (𝓝 m) (𝓝 0) := by
      simpa only [nhdsWithin_univ] using
        Real.taylor_tendsto convex_univ (mem_univ m) hφ.contDiffOn
    exact hTaylor.comp hz
  have hzero : Tendsto (fun n : ℕ => u^2 *
      ((φ (z n) - taylorWithinEval φ 2 univ m (z n)) / (z n-m)^2))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using ht.const_mul (u^2)
  have heq (n : ℕ) :
      u^2 * ((φ (z n) - taylorWithinEval φ 2 univ m (z n)) / (z n-m)^2) =
      (n+2 : ℕ) * (φ (z n)-φ m) - q*u^2/2 := by
    have hs : Real.sqrt (n+2 : ℕ) ≠ 0 := (sqrt_dim_pos n).ne'
    have hn : ((n+2 : ℕ) : ℝ) ≠ 0 := by positivity
    by_cases hu : u=0
    · subst u; simp [z]
    · have hz0 : z n-m ≠ 0 := by
        dsimp [z]; rw [add_sub_cancel_left]; exact div_ne_zero hu hs
      have hscale : u^2 = ((n+2 : ℕ) : ℝ) * (z n-m)^2 := by
        dsimp [z]
        rw [add_sub_cancel_left, div_pow, Real.sq_sqrt (show 0 ≤ ((n+2 : ℕ) : ℝ) by positivity)]
        field_simp
      calc
        _ = ((n+2 : ℕ) : ℝ) * (φ (z n)-taylorWithinEval φ 2 univ m (z n)) := by
          rw [hscale]
          field_simp [hz0]
        _ = ((n+2 : ℕ) : ℝ) * (φ (z n)-φ m)-q*u^2/2 := by
          rw [taylor_poly_two hstat hcurv]
          rw [hscale]
          ring
  convert hzero.add_const (q*u^2/2) using 1
  · funext n; rw [heq]; ring
  · ring

end
end SlowEquilibration.SourceGaussianLaplaceTaylor
