-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianDiagonalQuadraticVariance
public import SlowEquilibration.Upstream.OAI.MathematicalPhysics.CriticalSK.GaussianMoments
public import SlowEquilibration.NonnegativeRealMoment
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Genuine centered Gaussian quadratic exponential moments. The exact
scalar Gaussian integral and true product Gaussian law yield dimension
independent normalized exponential control, for either sign of each weight. -/
@[expose] public section
namespace SlowEquilibration.GaussianQuadraticVariance
noncomputable section
open Function MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

lemma centered_square_exp_integrable {t : ℝ} (ht : t < 1/2) :
    Integrable (fun x:ℝ=>Real.exp (t*(x^2-1))) γ := by
  have heq (x:ℝ) : Real.exp (t*(x^2-1))=Real.exp (-t)*Real.exp (t*x^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [heq]
  exact (OAI.CriticalSK.gaussian_square_integrable t ht).const_mul _

lemma centered_square_exp_integral {t : ℝ} (ht : t < 1/2) :
    (∫ x:ℝ,Real.exp (t*(x^2-1)) ∂γ)=Real.exp (-t)/(Real.sqrt (1-2*t)) := by
  have heq (x:ℝ) : Real.exp (t*(x^2-1))=Real.exp (-t)*Real.exp (t*x^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [heq,integral_const_mul,OAI.CriticalSK.gaussian_square_integral t ht,div_eq_mul_inv]

/-- The centered scalar log MGF has a true quadratic budget for both
positive and negative arguments, with no concentration hypothesis. -/
lemma centered_square_exp_integral_le {t : ℝ} (ht : |t| ≤ 1/4) :
    (∫ x:ℝ,Real.exp (t*(x^2-1)) ∂γ) ≤ Real.exp (4*t^2) := by
  have htUpper : t < 1/2:=lt_of_le_of_lt (le_abs_self t) (ht.trans_lt (by norm_num))
  have hArg : 0 < 1-2*t:=by linarith
  have hSmall : |2*t| < 1 := by rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)];nlinarith
  have hLog:=Real.abs_log_sub_add_sum_range_le hSmall 1
  norm_num only [Finset.sum_range_one,pow_one,Nat.cast_zero,Nat.cast_one,zero_add,div_one] at hLog
  have hDen : 0 < 1-|2*t| := by linarith
  have hDenHalf : (1/2:ℝ) ≤ 1-|2*t| := by
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  have hRem : |Real.log (1-2*t)+2*t| ≤ 8*t^2 := by
    have hLog' : |Real.log (1-2*t)+2*t| ≤ |2*t|^2/(1-|2*t|) := by simpa only [add_comm] using hLog
    apply hLog'.trans
    apply (div_le_iff₀ hDen).mpr
    have hNum : |2*t|^2=4*t^2 := by rw [sq_abs];ring
    rw [hNum]
    nlinarith [mul_le_mul_of_nonneg_left hDenHalf (sq_nonneg t)]
  have hBound : -t-Real.log (1-2*t)/2 ≤ 4*t^2 := by
    have hh:=neg_abs_le (Real.log (1-2*t)+2*t)
    linarith
  rw [centered_square_exp_integral htUpper]
  have hEq : Real.exp (-t)/Real.sqrt (1-2*t)=Real.exp (-t-Real.log (1-2*t)/2) := by
    rw [Real.exp_sub,← Real.log_sqrt hArg.le,Real.exp_log (Real.sqrt_pos.mpr hArg)]
  rw [hEq]
  exact Real.exp_le_exp.mpr hBound

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every deterministic weighted centered square sum has a true
exponential moment from its independent actual Gaussian coordinates. -/
theorem diagonalQuadratic_exp_integral_le (w : ι → ℝ) (t : ℝ)
    (hSmall : ∀ i,|t*w i| ≤ 1/4) :
    Integrable (fun x=>Real.exp (t*diagonalQuadratic w x)) (γpi ι) ∧
      (∫ x,Real.exp (t*diagonalQuadratic w x) ∂γpi ι) ≤
        Real.exp (4*t^2*(∑ i,w i^2)) := by
  have heq (x:ι→ℝ) : Real.exp (t*diagonalQuadratic w x)=
      ∏ i,Real.exp ((t*w i)*(x i^2-1)) := by
    unfold diagonalQuadratic centeredSquare
    rw [Finset.mul_sum,Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i hi
    congr 1
    ring
  have hI (i:ι) : Integrable (fun x:ℝ=>Real.exp ((t*w i)*(x^2-1))) γ :=
    centered_square_exp_integrable (lt_of_le_of_lt (le_abs_self _) ((hSmall i).trans_lt (by norm_num)))
  constructor
  · simp only [heq]
    exact Integrable.fintype_prod hI
  · simp only [heq,γpi]
    rw [integral_fintype_prod_eq_prod (μ:=fun _ : ι=>γ) (fun (i:ι) (x:ℝ)=>Real.exp ((t*w i)*(x^2-1)))]
    calc
      _ ≤ ∏ i,Real.exp (4*(t*w i)^2) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact integral_nonneg (fun _=>Real.exp_nonneg _)
        · intro i hi
          exact centered_square_exp_integral_le (hSmall i)
      _=Real.exp (4*t^2*(∑ i,w i^2)) := by
        rw [← Real.exp_sum,Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        ring

end
end SlowEquilibration.GaussianQuadraticVariance
