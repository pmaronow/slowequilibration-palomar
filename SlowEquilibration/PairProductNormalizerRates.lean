-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairDependentProductComparison

/-! Quantitative replacement of true Schur-weighted bulk means by the
literal adjacent one-point GOE means in dependent product comparisons. -/
@[expose] public section
namespace SlowEquilibration.PairSchurExpectation
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

theorem product_normalizer_rate {I lambda1 lambda2 A t E:ℝ}
    (hA:0 ≤ A) (ht:0 ≤ t) (hE:0 ≤ E) (hSmall:A*t ≤ 1/2)
    (hlambda1:|lambda1-1| ≤ A*t) (hlambda2:|lambda2-1| ≤ A*t) (hI:|I-1| ≤ E) :
    |I/(lambda1*lambda2)-1| ≤ 4*(E+3*A*t):=by
  have hlambda1low:(1/2:ℝ) ≤ lambda1:=by have hh:=(abs_le.mp hlambda1).1;nlinarith
  have hlambda2low:(1/2:ℝ) ≤ lambda2:=by have hh:=(abs_le.mp hlambda2).1;nlinarith
  have hDen:(1/4:ℝ) ≤ lambda1*lambda2:=by nlinarith
  have hDenPos:0<lambda1*lambda2:=lt_of_lt_of_le (by norm_num) hDen
  have hAt:0 ≤ A*t:=mul_nonneg hA ht
  have hProd:|lambda1*lambda2-1| ≤ 3*A*t:=by
    have he:lambda1*lambda2-1=(lambda1-1)*(lambda2-1)+(lambda1-1)+(lambda2-1):=by ring
    rw [he]
    calc
      _ ≤ |lambda1-1| *|lambda2-1| +|lambda1-1| +|lambda2-1|:=by
        calc
          _ ≤ |(lambda1-1)*(lambda2-1)+(lambda1-1)|+|lambda2-1|:=abs_add_le _ _
          _ ≤ |(lambda1-1)*(lambda2-1)|+|lambda1-1|+|lambda2-1|:=by
            have hh:=abs_add_le ((lambda1-1)*(lambda2-1)) (lambda1-1)
            linarith
          _=_:=by rw [abs_mul]
      _ ≤ (A*t)^2+2*(A*t):=by
        have hm:=mul_le_mul hlambda1 hlambda2 (abs_nonneg _) hAt
        nlinarith
      _ ≤ _:=by nlinarith
  have hNum:|I-lambda1*lambda2| ≤ E+3*A*t:=by
    have he:I-lambda1*lambda2=(I-1)-(lambda1*lambda2-1):=by ring
    rw [he]
    exact (abs_sub _ _).trans (add_le_add hI hProd)
  rw [show I/(lambda1*lambda2)-1=(I-lambda1*lambda2)/(lambda1*lambda2) by field_simp,
    abs_div,abs_of_pos hDenPos]
  calc
    _ ≤ (E+3*A*t)/(lambda1*lambda2):=div_le_div_of_nonneg_right hNum hDenPos.le
    _ ≤ (E+3*A*t)/(1/4:ℝ):=div_le_div_of_nonneg_left (by positivity) (by norm_num) hDen
    _=_:=by ring

end
end SlowEquilibration.PairSchurExpectation
