-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianQuadraticNormalizedExponential

/-! Genuine every fixed real moment of a centered Gaussian quadratic form,
with the sharp dimension factor sqrt(m) times its spectral weight bound. -/
@[expose] public section
namespace SlowEquilibration.GaussianQuadraticVariance
noncomputable section
open Function MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

def quadraticMomentConstant (q : ℝ) : ℝ := 1+2*((Nat.ceil q).factorial:ℝ)*Real.exp (1/4:ℝ)

lemma quadraticMomentConstant_pos (q : ℝ) : 0 < quadraticMomentConstant q := by
  unfold quadraticMomentConstant
  positivity

/-- Positive and negative exponential integrals dominate actual absolute
integer moments on the original probability space. -/
lemma integer_absolute_moment_of_exponential {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : Measurable f) (r : ℕ)
    (hPos : Integrable (fun x=>Real.exp (f x)) μ)
    (hNeg : Integrable (fun x=>Real.exp (-f x)) μ) :
    Integrable (fun x=>|f x|^r) μ ∧
      (∫ x,|f x|^r ∂μ) ≤ (r.factorial:ℝ)*
        ((∫ x,Real.exp (f x) ∂μ)+(∫ x,Real.exp (-f x) ∂μ)) := by
  have hFact : 0 < (r.factorial:ℝ):=Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hExp (x) : Real.exp |f x| ≤ Real.exp (f x)+Real.exp (-f x) := by
    by_cases hx : 0 ≤ f x
    · rw [abs_of_nonneg hx]
      exact le_add_of_nonneg_right (Real.exp_nonneg _)
    · rw [abs_of_neg (lt_of_not_ge hx)]
      exact le_add_of_nonneg_left (Real.exp_nonneg _)
  have hp (x) : |f x|^r ≤ (r.factorial:ℝ)*(Real.exp (f x)+Real.exp (-f x)) := by
    have hh:=(div_le_iff₀ hFact).mp (Real.pow_div_factorial_le_exp |f x| (abs_nonneg _) r)
    exact hh.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hExp x) hFact.le)
  have hdom:= (hPos.add hNeg).const_mul (r.factorial:ℝ)
  have hi : Integrable (fun x=>|f x|^r) μ :=
    hdom.mono' (hf.abs.pow_const r).aestronglyMeasurable
      (ae_of_all _ (fun x=>by rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _)];exact hp x))
  refine ⟨hi,(integral_mono hi hdom hp).trans_eq ?_⟩
  simp only [integral_const_mul,Pi.add_apply]
  rw [integral_add hPos hNeg]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pointwise deterministic spectral weights imply the genuine sharp
centered every-real-q moment. The constants do not depend on the Gaussian
coordinate dimension or on the signs of the eigenvalues. -/
theorem diagonalQuadratic_high_moment (w : ι → ℝ) {L : ℝ} (hL : 0 < L)
    (hm : 0 < Fintype.card ι) (hw : ∀ i,|w i| ≤ L) (q : ℝ) (hq : 0 ≤ q) :
    Integrable (fun x=>|diagonalQuadratic w x|^q) (γpi ι) ∧
      (∫ x,|diagonalQuadratic w x|^q ∂γpi ι) ≤
        quadraticMomentConstant q*(quadraticFluctuationScale (Fintype.card ι) L)^q := by
  let a:=quadraticFluctuationScale (Fintype.card ι) L
  have ha : 0 < a:=quadraticFluctuationScale_pos hm hL
  let f:=fun x:ι→ℝ=>diagonalQuadratic w x/a
  have hf : Measurable f := by unfold f diagonalQuadratic centeredSquare;fun_prop
  have hExp : Integrable (fun x=>Real.exp (f x)) (γpi ι) ∧
      Integrable (fun x=>Real.exp (-f x)) (γpi ι) ∧
      (∫ x,Real.exp (f x) ∂γpi ι) ≤ Real.exp (1/4:ℝ) ∧
      (∫ x,Real.exp (-f x) ∂γpi ι) ≤ Real.exp (1/4:ℝ) := by
    simpa only [f,a,neg_div] using diagonalQuadratic_normalized_exp w hL hm hw
  have hInt:=integer_absolute_moment_of_exponential (γpi ι) f hf (Nat.ceil q) hExp.1 hExp.2.1
  have hIntBound : (∫ x,|f x|^(Nat.ceil q) ∂γpi ι) ≤
      2*((Nat.ceil q).factorial:ℝ)*Real.exp (1/4:ℝ) := by
    refine hInt.2.trans ?_
    have hh:=mul_le_mul_of_nonneg_left (add_le_add hExp.2.2.1 hExp.2.2.2)
      (Nat.cast_nonneg (Nat.ceil q).factorial)
    nlinarith [hh]
  have hReal:=NonnegativeRealMoment.real_moment_of_integer (γpi ι) (fun x=>|f x|) hf.abs
    (fun _=>abs_nonneg _) hq (Nat.ceil q) (Nat.le_ceil q) hInt.1
  have hBound : (∫ x,|f x|^q ∂γpi ι) ≤ quadraticMomentConstant q :=
    hReal.2.trans (add_le_add le_rfl hIntBound)
  have hEq (x) : |diagonalQuadratic w x|^q=a^q*|f x|^q := by
    have hAbs : |diagonalQuadratic w x|=a*|f x| := by
      dsimp only [f]
      rw [abs_div,abs_of_pos ha]
      field_simp
    rw [hAbs,Real.mul_rpow ha.le (abs_nonneg _)]
  refine ⟨by simpa only [hEq] using hReal.1.const_mul (a^q),?_⟩
  simp only [hEq,integral_const_mul]
  have hh:=mul_le_mul_of_nonneg_left hBound (Real.rpow_nonneg ha.le q)
  simpa only [mul_comm] using hh

end
end SlowEquilibration.GaussianQuadraticVariance
