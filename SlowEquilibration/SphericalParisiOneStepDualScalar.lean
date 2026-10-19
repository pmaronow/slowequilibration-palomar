-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiLabeledCovariance

@[expose] public section

/-! Exact stationary one-step dual/primal algebra. These are scalar
identities under literal analytic stationarity equations, not supplied
physical pressure/ground-state conclusions. Establishing actual global
primal minimization and the genuine physical upper remains separate. -/

namespace SlowEquilibration.SphericalParisiOneStepDualScalar
noncomputable section
open SphericalParisiLabeledCovariance
set_option maxHeartbeats 1000000
variable {σ : Type*} [Fintype σ]

def oneStepDual (d : σ → ℕ) (c : σ → ℝ) (α q κ : ℝ) : ℝ :=
  κ/2+Real.log (κ/(κ-α*(xi1 d c 1-xi1 d c q)))/(2*α)+
    xi1 d c q/(2*(κ-α*(xi1 d c 1-xi1 d c q)))-α*(theta d c 1-theta d c q)/2

/-- Coupled scalar stationarity makes the actual dual moment margin1/L. -/
theorem stationary_dual_margin (d : σ → ℕ) (c : σ → ℝ)
    {α q L b : ℝ} (hL : 0 < L) (hb : 0 < b) (hB : b=L-α*(1-q))
    (hDelta : xi1 d c 1-xi1 d c q=(1-q)/(L*b)) :
    1/b-α*(xi1 d c 1-xi1 d c q)=1/L := by
  rw [hDelta]
  apply (mul_right_cancel₀ (show L*b ≠ 0 by positivity))
  field_simp
  linarith [hB]

/-- The actual positive determinant ratio at stationary parameters isL/b. -/
theorem stationary_dual_ratio (d : σ → ℕ) (c : σ → ℝ)
    {α q L b : ℝ} (hL : 0 < L) (hb : 0 < b) (hB : b=L-α*(1-q))
    (hDelta : xi1 d c 1-xi1 d c q=(1-q)/(L*b)) :
    (1/b)/(1/b-α*(xi1 d c 1-xi1 d c q))=L/b := by
  rw [stationary_dual_margin d c hL hb hB hDelta]
  field_simp

/-- Literal dual equality to the evaluated positive piecewise-affine
primal trial, including linear covariance and any odd degrees. The two
stationarity equations are essential; no pointwise same-q equality is
asserted without them. -/
theorem stationary_dual_eq_primal_expression (d : σ → ℕ) (c : σ → ℝ)
    {α q L b : ℝ} (hα : 0 < α) (hL : 0 < L) (hb : 0 < b) (hB : b=L-α*(1-q))
    (hQ : xi1 d c q=q/L^2) (hDelta : xi1 d c 1-xi1 d c q=(1-q)/(L*b)) :
    oneStepDual d c α q (1/b)=
      (b*xi1 d c 1+α*(xi d c 1-xi d c q)+q/L+Real.log (L/b)/α)/2 := by
  have h1 : xi1 d c 1=q/L^2+(1-q)/(L*b) := by linarith [hQ,hDelta]
  unfold oneStepDual
  rw [stationary_dual_ratio d c hL hb hB hDelta,
    stationary_dual_margin d c hL hb hB hDelta]
  unfold theta
  rw [hQ,h1]
  simp only [one_mul]
  rw [hB]
  have hbn : L-α*(1-q) ≠ 0 := by rw [← hB];exact hb.ne'
  field_simp [hα.ne',hL.ne',hbn]
  ring

end
end SlowEquilibration.SphericalParisiOneStepDualScalar
