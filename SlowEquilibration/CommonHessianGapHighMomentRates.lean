-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SchurDimensionRates

/-! Every fixed real power controls the genuine exponential gap loss. -/
@[expose] public section
namespace SlowEquilibration.SchurDimensionRates
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

def gapMomentConstant (a q:ℝ):ℝ:=
  ((Nat.ceil q).factorial:ℝ)*(3/(a^2/(32*Real.pi^2)))^(Nat.ceil q)

lemma sqrt_exp_gap_le_ambient_q (n:ℕ) {a q:ℝ} (ha:0<a) (hq:0 ≤ q):
    Real.sqrt (Real.exp (-(n+1:ℝ)*a^2/(16*Real.pi^2))) ≤
      gapMomentConstant a q*(1/Real.sqrt (n+3:ℕ))^q:=by
  let c:=a^2/(32*Real.pi^2)
  let m:=Nat.ceil q
  have hc:0<c:=by dsimp only [c];positivity [Real.pi_pos]
  have hN:0<(n+1:ℝ):=by positivity
  have hRoot:0<Real.sqrt (n+3:ℕ):=by positivity
  have hExp:Real.sqrt (Real.exp (-(n+1:ℝ)*a^2/(16*Real.pi^2)))=
      Real.exp (-(c*(n+1:ℝ))):=by
    rw [GOEEdgePolynomialRate.sqrt_exp_eq]
    congr 1
    dsimp only [c]
    ring
  have hTaylor:=Real.pow_div_factorial_le_exp (c*(n+1:ℝ)) (by positivity) m
  have hPower:0<(c*(n+1:ℝ))^m:=by positivity
  have hFact:0<(m.factorial:ℝ):=Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hExpBound:Real.exp (-(c*(n+1:ℝ))) ≤ (m.factorial:ℝ)/(c*(n+1:ℝ))^m:=by
    rw [Real.exp_neg,inv_eq_one_div]
    have hh:=one_div_le_one_div_of_le (div_pos hPower hFact) hTaylor
    exact hh.trans_eq (by field_simp)
  have hInv:(1/(n+1:ℝ)) ≤ 3/Real.sqrt (n+3:ℕ):=by
    simpa only [mul_one] using inverse_dimension_le_ambient_inverse_sqrt n (C:=1) (by norm_num)
  have hInvPow:((1:ℝ)/(n+1:ℝ))^m ≤ (3/Real.sqrt (n+3:ℕ))^m:=pow_le_pow_left₀ (by positivity) hInv _
  have hScale:(m.factorial:ℝ)/(c*(n+1:ℝ))^m ≤
      (m.factorial:ℝ)*(3/c)^m*(1/Real.sqrt (n+3:ℕ))^m:=by
    have hh:=mul_le_mul_of_nonneg_left hInvPow (show 0 ≤ (m.factorial:ℝ)/c^m by positivity)
    convert hh using 1 <;> simp only [div_pow,mul_pow,one_pow] <;> ring
  have hBase:(1/Real.sqrt (n+3:ℕ)) ≤ 1:=by
    apply (div_le_one hRoot).mpr
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by norm_cast;omega)
  have hRpow:((1:ℝ)/Real.sqrt (n+3:ℕ))^m ≤ (1/Real.sqrt (n+3:ℕ))^q:=by
    rw [←Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge (by positivity) hBase (Nat.le_ceil q)
  rw [hExp]
  exact (hExpBound.trans hScale).trans
    (mul_le_mul_of_nonneg_left hRpow (by positivity))

end
end SlowEquilibration.SchurDimensionRates
