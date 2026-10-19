-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.BorderSchurExpectation

/-! Ordinary dependent-product error from actual same-space L2 errors.
No independence of the complete bordered determinants is assumed. -/
@[expose] public section
namespace SlowEquilibration.PairSchurExpectation
noncomputable section
open Function MeasureTheory ProbabilityTheory
open BorderSchurExpectation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

theorem dependent_product_comparison {Ω:Type*} [MeasurableSpace Ω] (P:Measure Ω)
    (F1 F2 B1 B2:Ω→ℝ) (hF1:MemLp F1 2 P) (hF2:MemLp F2 2 P)
    (hB1:MemLp B1 2 P) (hB2:MemLp B2 2 P) :
    Integrable (fun x=>|F1 x*F2 x-B1 x*B2 x|) P ∧
      (∫ x,|F1 x*F2 x-B1 x*B2 x| ∂P) ≤
        Real.sqrt (∫ x,(F1 x-B1 x)^2 ∂P)*Real.sqrt (∫ x,F2 x^2 ∂P)+
        Real.sqrt (∫ x,B1 x^2 ∂P)*Real.sqrt (∫ x,(F2 x-B2 x)^2 ∂P):=by
  have hE1:=hF1.sub hB1
  have hE2:=hF2.sub hB2
  have hP1:Integrable (fun x=>(F1 x-B1 x)*F2 x) P:=memLp_one_iff_integrable.mp (hE1.mul hF2)
  have hP2:Integrable (fun x=>B1 x*(F2 x-B2 x)) P:=memLp_one_iff_integrable.mp (hB1.mul hE2)
  have he (x):F1 x*F2 x-B1 x*B2 x=(F1 x-B1 x)*F2 x+B1 x*(F2 x-B2 x):=by ring
  have hI:Integrable (fun x=>|F1 x*F2 x-B1 x*B2 x|) P:=by
    simpa only [he,Pi.add_apply] using (hP1.add hP2).abs
  have hR:Integrable (fun x=>|F1 x-B1 x| *|F2 x| +|B1 x| *|F2 x-B2 x|) P:=by
    convert hP1.abs.add hP2.abs using 1
    ext x
    simp only [Pi.add_apply,abs_mul]
  refine ⟨hI,(integral_mono hI hR (fun x=>by rw [he];simpa only [abs_mul] using abs_add_le ((F1 x-B1 x)*F2 x) (B1 x*(F2 x-B2 x)))).trans ?_⟩
  have hSplit:=integral_add (f:=fun x=>|F1 x-B1 x| *|F2 x|) (g:=fun x=>|B1 x| *|F2 x-B2 x|)
    (by simpa only [abs_mul] using hP1.abs) (by simpa only [abs_mul] using hP2.abs)
  rw [hSplit]
  exact add_le_add (integral_abs_mul_le_sqrt_sq hE1 hF2) (integral_abs_mul_le_sqrt_sq hB1 hE2)

theorem dependent_product_second_moment {Ω:Type*} [MeasurableSpace Ω] (P:Measure Ω)
    (F1 F2:Ω→ℝ) (hF1:Measurable F1) (hF2:Measurable F2)
    (hF14:Integrable (fun x=>F1 x^4) P) (hF24:Integrable (fun x=>F2 x^4) P) :
    Integrable (fun x=>(F1 x*F2 x)^2) P ∧
      (∫ x,(F1 x*F2 x)^2 ∂P) ≤ Real.sqrt (∫ x,F1 x^4 ∂P)*Real.sqrt (∫ x,F2 x^4 ∂P):=by
  have h1:MemLp (fun x=>F1 x^2) 2 P:=(memLp_two_iff_integrable_sq (hF1.pow_const 2).aestronglyMeasurable).mpr
    (by simpa only [←pow_mul,show (2:ℕ)*2=4 by norm_num] using hF14)
  have h2:MemLp (fun x=>F2 x^2) 2 P:=(memLp_two_iff_integrable_sq (hF2.pow_const 2).aestronglyMeasurable).mpr
    (by simpa only [←pow_mul,show (2:ℕ)*2=4 by norm_num] using hF24)
  have hI:Integrable (fun x=>(F1 x*F2 x)^2) P:=by
    convert memLp_one_iff_integrable.mp (h1.mul h2) using 1
    ext x
    simp only [Pi.mul_apply,mul_pow]
  refine ⟨hI,?_⟩
  have hh:=integral_abs_mul_le_sqrt_sq h1 h2
  simpa only [abs_pow,sq_abs,mul_pow,←pow_mul,show (2:ℕ)*2=4 by norm_num] using hh

end
end SlowEquilibration.PairSchurExpectation
