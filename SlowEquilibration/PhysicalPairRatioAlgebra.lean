-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairPhysicalDensitySourceRatios
public import SlowEquilibration.PairGradientDensitySharp

/-! Scalar multiplication of the actual gradient, physical mark, and
intrinsic determinant ratios. Positivity is used only for the logarithms;
no independence of the actual Hessian determinants is introduced. -/
@[expose] public section
namespace SlowEquilibration.PairSchurExpectation
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

lemma pair_ratio_error_of_log_bounds {g v D A B E:ℝ} (hg:0<g) (hv:0<v)
    (hA:0 ≤ A) (hB:0 ≤ B) (_hE:0 ≤ E)
    (hG:|Real.log g| ≤ A) (hV:|Real.log v| ≤ B) (hD:|D-1| ≤ E)
    (hSmall:A+B ≤ 1) (hESmall:E ≤ 1) :
    |g*v*D-1| ≤ 4*(A+B)+E:=by
  have hLog:|Real.log (g*v)| ≤ A+B:=by
    rw [Real.log_mul hg.ne' hv.ne']
    exact (abs_add_le _ _).trans (add_le_add hG hV)
  have hGV:|g*v-1| ≤ 2*(A+B):=by
    rw [←Real.exp_log (mul_pos hg hv)]
    exact (Real.abs_exp_sub_one_le (hLog.trans hSmall)).trans (mul_le_mul_of_nonneg_left hLog (by norm_num))
  have hDabs:|D| ≤ 1+E:=by
    have hh:=abs_add_le (D-1) 1
    rw [sub_add_cancel,abs_one] at hh
    linarith
  have he:g*v*D-1=(g*v-1)*D+(D-1):=by ring
  rw [he]
  calc
    _ ≤ |g*v-1| *|D| +|D-1|:=by simpa only [abs_mul] using abs_add_le ((g*v-1)*D) (D-1)
    _ ≤ (2*(A+B))*(1+E)+E:=by
      exact add_le_add (mul_le_mul hGV hDabs (abs_nonneg _) (by positivity)) hD
    _ ≤ _:=by nlinarith

lemma pair_ratio_upper_of_log_bounds {g v D A B E:ℝ} (hg:0<g) (hv:0<v)
    (hE:0 ≤ E) (hG:|Real.log g| ≤ A) (hV:|Real.log v| ≤ B) (hD:|D-1| ≤ E) :
    g*v*D ≤ (1+E)*Real.exp (A+B):=by
  have hGV:g*v ≤ Real.exp (A+B):=by
    rw [←Real.exp_log (mul_pos hg hv)]
    apply Real.exp_le_exp.mpr
    rw [Real.log_mul hg.ne' hv.ne']
    exact add_le_add ((le_abs_self _).trans hG) ((le_abs_self _).trans hV)
  have hDu:D ≤ 1+E:=by have hh:=(le_abs_self (D-1)).trans hD;linarith
  calc
    g*v*D ≤ g*v*(1+E):=mul_le_mul_of_nonneg_left hDu (mul_pos hg hv).le
    _ ≤ Real.exp (A+B)*(1+E):=mul_le_mul_of_nonneg_right hGV (by positivity)
    _=_:=by ring

end
end SlowEquilibration.PairSchurExpectation
