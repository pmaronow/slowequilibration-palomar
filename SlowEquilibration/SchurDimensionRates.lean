-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEEdgePolynomialRate

/-! Deterministic conversion of the true exponential gap term and Schur
variance budget to the manuscript's ambient inverse-square-root rate. -/
@[expose] public section
namespace SlowEquilibration.SchurDimensionRates
noncomputable section

lemma sqrt_exp_gap_le_inverse_dimension (n : ℕ) {a : ℝ} (ha : 0 < a) :
    Real.sqrt (Real.exp (-(n+1:ℝ)*a^2/(16*Real.pi^2))) ≤
      (32*Real.pi^2/a^2)/(n+1:ℝ) := by
  let c:=a^2/(32*Real.pi^2)
  have hc : 0 < c:=by dsimp only [c];positivity [Real.pi_pos]
  have hN : 0 < (n+1:ℝ):=by positivity
  rw [GOEEdgePolynomialRate.sqrt_exp_eq]
  have he : (-(n+1:ℝ)*a^2/(16*Real.pi^2))/2=-(c*(n+1:ℝ)) := by dsimp only [c];ring
  rw [he]
  have hh:=Real.mul_exp_neg_le_exp_neg_one (c*(n+1:ℝ))
  have hOne : Real.exp (-1:ℝ) ≤ 1:=by simpa using Real.exp_le_exp.mpr (by norm_num : (-1:ℝ)≤0)
  apply (le_div_iff₀ hN).mpr
  have hcInv : 32*Real.pi^2/a^2=c⁻¹ := by dsimp only [c];field_simp
  rw [hcInv,inv_eq_one_div]
  apply (le_div_iff₀ hc).mpr
  nlinarith [hh.trans hOne]

lemma inverse_dimension_le_ambient_inverse_sqrt (n : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    C/(n+1:ℝ) ≤ 3*C/Real.sqrt (n+3:ℕ) := by
  have hN : 0 < Real.sqrt (n+3:ℕ) := by positivity
  have hn : 0 < (n+1:ℝ):=by positivity
  have hRoot : Real.sqrt (n+3:ℕ) ≤ 3*(n+1:ℝ) := by
    have hOne : (1:ℝ)≤(n+3:ℕ) := by norm_cast;omega
    have hh : Real.sqrt (n+3:ℕ) ≤ (n+3:ℕ) := (Real.sqrt_le_left (by positivity)).mpr (by nlinarith)
    exact hh.trans (by simp only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_one];nlinarith [Nat.cast_nonneg (α:=ℝ) n])
  apply (div_le_div_iff₀ hn hN).mpr
  nlinarith [mul_le_mul_of_nonneg_left hRoot hC]

end
end SlowEquilibration.SchurDimensionRates
