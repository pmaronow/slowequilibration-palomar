module
-- SPDX-License-Identifier: Apache-2.0

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic

@[expose] public section

/-! # Actual eventual absorption of the dimension factor in energy bounds -/
namespace SlowEquilibration
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology

/-- A true exponential absorbs the linear dimension factor at half its
positive decay rate. The threshold is chosen before every model input. -/
theorem linear_exponential_absorption {a : ℝ} (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop, (N:ℝ)*Real.exp (-a*(N:ℝ)) ≤
      Real.exp (-(a/2)*(N:ℝ)) := by
  have ht : Tendsto (fun N : ℕ => (N:ℝ)*Real.exp (-(a/2)*(N:ℝ))) atTop (𝓝 (0:ℝ)) := by
    convert (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) (a/2) (by positivity)).comp
      tendsto_natCast_atTop_atTop using 1
    ext N
    simp only [Function.comp_apply, Real.rpow_one]
  filter_upwards [ht.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num))] with N hN
  have he : Real.exp (-a*(N:ℝ)) =
      Real.exp (-(a/2)*(N:ℝ))*Real.exp (-(a/2)*(N:ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, ← mul_assoc]
  exact (mul_le_mul_of_nonneg_right hN.le (Real.exp_pos _).le).trans_eq (one_mul _)

/-- Both actual deterministic error rates feed one true uniform eventual
energy estimate with a positive, dimension-independent coefficient. -/
theorem dimension_times_two_exponentials_eventually {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (M : ℝ) :
    ∀ᶠ N : ℕ in atTop, 4*(N:ℝ)*M^2*(Real.exp (-a*(N:ℝ))+Real.exp (-b*(N:ℝ))) ≤
      8*(M^2+1)*Real.exp (-(min a b/2)*(N:ℝ)) := by
  have hs : 0 < min a b := lt_min ha hb
  filter_upwards [linear_exponential_absorption hs] with N hN
  have hA : Real.exp (-a*(N:ℝ)) ≤ Real.exp (-min a b*(N:ℝ)) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right (min_le_left a b) (Nat.cast_nonneg (α:=ℝ) N)
    linarith
  have hB : Real.exp (-b*(N:ℝ)) ≤ Real.exp (-min a b*(N:ℝ)) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right (min_le_right a b) (Nat.cast_nonneg (α:=ℝ) N)
    linarith
  calc
    _ ≤ 4*(N:ℝ)*M^2*(2*Real.exp (-min a b*(N:ℝ))) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 8*M^2*((N:ℝ)*Real.exp (-min a b*(N:ℝ))) := by ring
    _ ≤ 8*M^2*Real.exp (-(min a b/2)*(N:ℝ)) :=
      mul_le_mul_of_nonneg_left hN (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg M]) (Real.exp_pos _).le

end
end SlowEquilibration
