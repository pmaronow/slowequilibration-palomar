-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairProductNormalizerTransfer

/-! Exact equivalence between normalized product expectations and the
source's literal quotient of the original product expectation by its two
one-point GOE means. -/
@[expose] public section
namespace SlowEquilibration.PairSchurExpectation
noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

theorem literal_product_integral_quotient {Ω:Type*} [MeasurableSpace Ω]
    (P:Measure Ω) (D1 D2:Ω→ℝ) {m1 m2:ℝ} (hm1:m1≠0) (hm2:m2≠0)
    (hI:Integrable (fun x=>(D1 x/m1)*(D2 x/m2)) P) :
    Integrable (fun x=>D1 x*D2 x) P ∧
      (∫ x,(D1 x/m1)*(D2 x/m2) ∂P)=(∫ x,D1 x*D2 x ∂P)/(m1*m2):=by
  have he (x):(D1 x/m1)*(D2 x/m2)=(D1 x*D2 x)/(m1*m2):=by
    simp only [div_eq_mul_inv,_root_.mul_inv_rev]
    ring
  have hRaw (x):D1 x*D2 x=((D1 x/m1)*(D2 x/m2))*(m1*m2):=by field_simp
  refine ⟨(hI.mul_const (m1*m2)).congr (.of_forall (fun x=>(hRaw x).symm)),?_⟩
  simp only [he,integral_div]

end
end SlowEquilibration.PairSchurExpectation
