-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairProductNormalizerRates

/-! Exact transfer for two dependent determinants when their two literal
one-point means replace their Schur-weighted common-bulk normalizers. -/
@[expose] public section
namespace SlowEquilibration.PairSchurExpectation
noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem dependent_product_normalizer_transfer {Ω:Type*} [MeasurableSpace Ω]
    (P:Measure Ω) (D1 D2:Ω→ℝ) {a1 a2 m1 m2 A t E:ℝ}
    (ha1:a1≠0) (ha2:a2≠0) (hm1:m1≠0) (hm2:m2≠0)
    (hA:0 ≤ A) (ht:0 ≤ t) (hE:0 ≤ E) (hSmall:A*t ≤ 1/2)
    (hlambda1:|m1/a1-1| ≤ A*t) (hlambda2:|m2/a2-1| ≤ A*t)
    (hI:Integrable (fun x=>(D1 x/a1)*(D2 x/a2)) P)
    (hError:|(∫ x,(D1 x/a1)*(D2 x/a2) ∂P)-1| ≤ E) :
    Integrable (fun x=>(D1 x/m1)*(D2 x/m2)) P ∧
      |(∫ x,(D1 x/m1)*(D2 x/m2) ∂P)-1| ≤ 4*(E+3*A*t):=by
  have he (x):(D1 x/m1)*(D2 x/m2)=((D1 x/a1)*(D2 x/a2))/((m1/a1)*(m2/a2)):=by
    field_simp
  refine ⟨by simpa only [he] using hI.div_const ((m1/a1)*(m2/a2)),?_⟩
  simp only [he,integral_div]
  exact product_normalizer_rate hA ht hE hSmall hlambda1 hlambda2 hError

end
end SlowEquilibration.PairSchurExpectation
