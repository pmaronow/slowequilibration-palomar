-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-! # The convex derivative comparison in the positivity perturbation

This proves the scalar estimate of Panchenko, arXiv:0708.2453v1, Lemma 2,
from actual convexity and ordinary differentiability. It is used to transfer
log-partition concentration to perturbation-energy self-averaging.
-/

namespace SlowEquilibration.GaussianPerturbationConvexity
open Set
set_option autoImplicit false
set_option maxHeartbeats 300000

/-- Close convex function values control derivative differences through
the derivative spread of one function on a small interval. -/
theorem abs_deriv_sub_le (θ ψ : ℝ → ℝ)
    (hθ : ConvexOn ℝ univ θ) (hψ : ConvexOn ℝ univ ψ)
    (hθd : Differentiable ℝ θ) (hψd : Differentiable ℝ ψ)
    (x : ℝ) {y : ℝ} (hy : 0 < y) :
    |deriv θ x-deriv ψ x| ≤ deriv ψ (x+y)-deriv ψ (x-y)+
      (|ψ (x+y)-θ (x+y)|+|ψ (x-y)-θ (x-y)|+|ψ x-θ x|)/y := by
  have hθp := hθ.le_slope_of_hasDerivAt (mem_univ x) (mem_univ (x+y))
    (by linarith) (hθd x).hasDerivAt
  have hθm := hθ.slope_le_of_hasDerivAt (mem_univ (x-y)) (mem_univ x)
    (by linarith) (hθd x).hasDerivAt
  have hψp := hψ.slope_le_of_hasDerivAt (mem_univ x) (mem_univ (x+y))
    (by linarith) (hψd (x+y)).hasDerivAt
  have hψm := hψ.le_slope_of_hasDerivAt (mem_univ (x-y)) (mem_univ x)
    (by linarith) (hψd (x-y)).hasDerivAt
  have hpEq : (x+y)-x=y := by ring
  have hmEq : x-(x-y)=y := by ring
  simp only [slope,vsub_eq_sub,smul_eq_mul] at hθp hθm hψp hψm
  rw [hpEq] at hθp hψp
  rw [hmEq] at hθm hψm
  have hθp' : deriv θ x*y ≤ θ (x+y)-θ x := by
    exact (le_div_iff₀ hy).mp (by simpa only [div_eq_mul_inv,mul_comm] using hθp)
  have hθm' : θ x-θ (x-y) ≤ deriv θ x*y := by
    exact (div_le_iff₀ hy).mp (by simpa only [div_eq_mul_inv,mul_comm] using hθm)
  have hψp' : ψ (x+y)-ψ x ≤ deriv ψ (x+y)*y := by
    exact (div_le_iff₀ hy).mp (by simpa only [div_eq_mul_inv,mul_comm] using hψp)
  have hψm' : deriv ψ (x-y)*y ≤ ψ x-ψ (x-y) := by
    exact (le_div_iff₀ hy).mp (by simpa only [div_eq_mul_inv,mul_comm] using hψm)
  have hmono := hψ.monotoneOn_deriv (fun z _ => hψd z)
  have hψlo := hmono (mem_univ (x-y)) (mem_univ x) (by linarith : x-y ≤ x)
  have hψhi := hmono (mem_univ x) (mem_univ (x+y)) (by linarith : x ≤ x+y)
  have hψlo' := mul_le_mul_of_nonneg_right hψlo hy.le
  have hψhi' := mul_le_mul_of_nonneg_right hψhi hy.le
  have hquot :
      ((|ψ (x+y)-θ (x+y)|+|ψ (x-y)-θ (x-y)|+|ψ x-θ x|)/y)*y =
      |ψ (x+y)-θ (x+y)|+|ψ (x-y)-θ (x-y)|+|ψ x-θ x| :=
    div_mul_cancel₀ _ hy.ne'
  rw [abs_le]
  constructor <;> nlinarith [le_abs_self (ψ x-θ x),neg_le_abs (ψ x-θ x),
    le_abs_self (ψ (x+y)-θ (x+y)),neg_le_abs (ψ (x+y)-θ (x+y)),
    le_abs_self (ψ (x-y)-θ (x-y)),neg_le_abs (ψ (x-y)-θ (x-y)),
    abs_nonneg (ψ (x+y)-θ (x+y)),abs_nonneg (ψ (x-y)-θ (x-y))]

end SlowEquilibration.GaussianPerturbationConvexity
