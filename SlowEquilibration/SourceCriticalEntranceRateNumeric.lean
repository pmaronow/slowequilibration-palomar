-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourceMixedCriticalEntranceHolderTransfer
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Deterministic rates in the critical-point transfer: the two source
entrance powers and exponential error reduce to one power, which then loses
the exact Hölder factor `1 - 1/r`. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceCriticalEntranceRateNumeric
open Filter
open SlowEquilibration.SphericalModel
set_option autoImplicit false

theorem entrance_exponential_le_power_eventually
    {c α : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-c*((n+1 : ℕ) : ℝ)) ≤
        ((n+1 : ℕ) : ℝ)^(-α) := by
  have hN : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hlim :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero α c hc).comp hN
  filter_upwards [hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
    with n hn
  let x : ℝ := ((n+1 : ℕ) : ℝ)
  have hx : 0 < x := by dsimp only [x]; positivity
  have hxp : 0 < x^α := Real.rpow_pos_of_pos hx α
  change x^α * Real.exp (-c*x) < 1 at hn
  have hdiv : Real.exp (-c*x) ≤ (x^α)⁻¹ := by
    have hmul : Real.exp (-c*x) * x^α ≤ 1 := by nlinarith
    simpa only [one_div] using (le_div_iff₀ hxp).mpr hmul
  change Real.exp (-c*x) ≤ x^(-α)
  simpa only [Real.rpow_neg hx.le] using hdiv

theorem entrance_source_rate_le_single_power_eventually
    {d c C : ℝ} (hd : 4 ≤ d) (hc : 0 < c) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      C*(((n+1 : ℕ) : ℝ)^(1-d/2)+
        ((n+1 : ℕ) : ℝ)^(3-d))+
        Real.exp (-c*((n+1 : ℕ) : ℝ)) ≤
      (2*C+1)*(((n+1 : ℕ) : ℝ)^(-(d-2)/2)) := by
  filter_upwards [entrance_exponential_le_power_eventually (α := (d-2)/2) hc,
    eventually_ge_atTop (0 : ℕ)] with n hExp _
  let x : ℝ := ((n+1 : ℕ) : ℝ)
  have hx : 1 ≤ x := by
    dsimp only [x]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hpow : x^(3-d) ≤ x^(1-d/2) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have heq : -(d-2)/2 = 1-d/2 := by ring
  have heq' : -((d-2)/2) = 1-d/2 := by ring
  change Real.exp (-c*x) ≤ x^(-((d-2)/2)) at hExp
  rw [heq'] at hExp
  rw [heq]
  change C*(x^(1-d/2)+x^(3-d))+Real.exp (-c*x) ≤
    (2*C+1)*x^(1-d/2)
  nlinarith [mul_nonneg hC (Real.rpow_nonneg (by positivity : 0 ≤ x) (1-d/2))]

end SlowEquilibration.SourceCriticalEntranceRateNumeric
