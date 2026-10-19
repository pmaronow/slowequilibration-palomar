-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianQuadraticUniformBound

/-! Exact dimension-free simplification of the genuine common-row
quadratic error bound in the physical variance-b/N normalization. -/
@[expose] public section
namespace SlowEquilibration.GaussianQuadraticVariance
noncomputable section
open Function MeasureTheory ProbabilityTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

/-- For min degree at least three, the proved actual Gaussian row error
is at most a fixed constant times N^-1 plus overlap squared. -/
theorem quadraticErrorBound_small_overlap {N m d : ℕ} (hN : 0 < N) (hmN : m ≤ N)
    (hd : 3 ≤ d) {b C D L r : ℝ} (hb : 0 ≤ b) (_hC : 0 ≤ C) (_hD : 0 ≤ D)
    (_hL : 0 ≤ L) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    quadraticErrorBound m (Real.sqrt (b/(N:ℝ))) (C/(N:ℝ)*r^(2*(d-2))) (D*r^(d-2)) L ≤
      L^2*(8*b^2/(N:ℝ)+(4*C^2+16*b*D^2+4*D^4)*r^2) := by
  have hNR : 0 < (N:ℝ):=Nat.cast_pos.mpr hN
  let a:ℝ:=(m:ℝ)/(N:ℝ)
  let q:=r^(d-2)
  have ha0 : 0 ≤ a:=div_nonneg (Nat.cast_nonneg _) hNR.le
  have ha1 : a ≤ 1:=(div_le_one hNR).mpr (by exact_mod_cast hmN)
  have hq0 : 0 ≤ q:=pow_nonneg hr0 _
  have hq : q ≤ r := by
    simpa only [pow_one] using pow_le_pow_of_le_one hr0 hr1 (show 1 ≤ d-2 by omega)
  have hq1 : q ≤ 1:=hq.trans hr1
  have haSq : a^2 ≤ 1:=by nlinarith [sq_nonneg a]
  have hqSq : q^2 ≤ r^2:=(sq_le_sq₀ hq0 hr0).mpr hq
  have hqSq1 : q^2 ≤ 1:=by nlinarith [sq_nonneg q]
  have hqFour : q^4 ≤ r^2 := by
    calc
      _=(q^2)^2:=by ring
      _ ≤ q^2:=by simpa only [pow_two] using mul_le_of_le_one_right (sq_nonneg q) hqSq1
      _ ≤ _:=hqSq
  have hsqrt : (Real.sqrt (b/(N:ℝ)))^2=b/(N:ℝ):=Real.sq_sqrt (div_nonneg hb hNR.le)
  have hfour : (Real.sqrt (b/(N:ℝ)))^4=(b/(N:ℝ))^2:=by
    rw [show (4:ℕ)=2*2 by norm_num,pow_mul,hsqrt]
  have heq : quadraticErrorBound m (Real.sqrt (b/(N:ℝ))) (C/(N:ℝ)*r^(2*(d-2))) (D*r^(d-2)) L=
      L^2*(8*b^2/(N:ℝ)*a+4*a^2*C^2*q^4+16*a*b*D^2*q^2+4*D^4*q^4) := by
    unfold quadraticErrorBound
    rw [hfour,hsqrt]
    dsimp only [a,q]
    rw [pow_mul r 2 (d-2)]
    field_simp
    ring
  rw [heq]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  calc
    _ ≤ 8*b^2/(N:ℝ)*1+4*1*C^2*r^2+16*1*b*D^2*r^2+4*D^4*r^2 := by
      apply add_le_add
      · apply add_le_add
        · exact add_le_add (mul_le_mul_of_nonneg_left ha1 (by positivity))
            (mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left haSq (by norm_num)) (sq_nonneg C))
              hqFour (by positivity) (by positivity))
        · gcongr
      · exact mul_le_mul_of_nonneg_left hqFour (by positivity)
    _=_:=by ring

end
end SlowEquilibration.GaussianQuadraticVariance

