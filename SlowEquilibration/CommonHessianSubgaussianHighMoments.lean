-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianQuadraticHighMoments
public import Mathlib.Probability.Moments.SubGaussian

/-! Genuine every-real-q ordinary moments from the actual two-sided
sub-Gaussian moment generating function at a chosen scaling. -/
@[expose] public section
namespace SlowEquilibration.GaussianQuadraticVariance
noncomputable section
open Function MeasureTheory ProbabilityTheory
open scoped NNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

def subgaussianMomentConstant (q B:ℝ):ℝ:=1+2*((Nat.ceil q).factorial:ℝ)*Real.exp B

lemma subgaussianMomentConstant_pos (q B:ℝ):0<subgaussianMomentConstant q B:=by
  unfold subgaussianMomentConstant;positivity

/-- No moment estimate is supplied: the actual MGF yields integrability
and the ordinary q-moment at inverse scale t. -/
theorem subgaussian_high_moment {Ω:Type*} [MeasurableSpace Ω] (P:Measure Ω)
    [IsProbabilityMeasure P] (F:Ω→ℝ) (hF:Measurable F) {c:ℝ≥0}
    (hG:HasSubgaussianMGF F c P) {t B:ℝ} (ht:0<t)
    (hBudget:(c:ℝ)*t^2/2≤B) (q:ℝ) (hq:0≤q) :
    Integrable (fun x=>|F x|^q) P ∧
      (∫ x,|F x|^q ∂P) ≤ subgaussianMomentConstant q B/t^q:=by
  let f:=fun x=>t*F x
  have hf:Measurable f:=measurable_const.mul hF
  have hPos:Integrable (fun x=>Real.exp (f x)) P:=hG.integrable_exp_mul t
  have hNeg:Integrable (fun x=>Real.exp (-f x)) P:=by
    simpa only [f,neg_mul] using hG.integrable_exp_mul (-t)
  have hPosBound:(∫ x,Real.exp (f x) ∂P)≤Real.exp B:=
    (hG.mgf_le t).trans (Real.exp_le_exp.mpr hBudget)
  have hNegBound:(∫ x,Real.exp (-f x) ∂P)≤Real.exp B:=by
    have hh:=(hG.mgf_le (-t)).trans (Real.exp_le_exp.mpr (by simpa only [neg_sq] using hBudget))
    simpa only [mgf,f,neg_mul] using hh
  have hInt:=integer_absolute_moment_of_exponential P f hf (Nat.ceil q) hPos hNeg
  have hIntBound:(∫ x,|f x|^(Nat.ceil q) ∂P)≤2*((Nat.ceil q).factorial:ℝ)*Real.exp B:=by
    have hh:=mul_le_mul_of_nonneg_left (add_le_add hPosBound hNegBound)
      (Nat.cast_nonneg (Nat.ceil q).factorial)
    exact hInt.2.trans (by nlinarith [hh])
  have hReal:=NonnegativeRealMoment.real_moment_of_integer P (fun x=>|f x|) hf.abs
    (fun _=>abs_nonneg _) hq (Nat.ceil q) (Nat.le_ceil q) hInt.1
  have hBound:(∫ x,|f x|^q ∂P) ≤ subgaussianMomentConstant q B:=
    hReal.2.trans (add_le_add le_rfl hIntBound)
  have hEq (x):|F x|^q=(t^q)⁻¹*|f x|^q:=by
    dsimp only [f]
    rw [abs_mul,abs_of_pos ht,Real.mul_rpow ht.le (abs_nonneg _)]
    field_simp
  refine ⟨by simpa only [hEq] using hReal.1.const_mul ((t^q)⁻¹),?_⟩
  simp only [hEq,integral_const_mul]
  exact (mul_le_mul_of_nonneg_left hBound (by positivity)).trans_eq (by ring)

end
end SlowEquilibration.GaussianQuadraticVariance
