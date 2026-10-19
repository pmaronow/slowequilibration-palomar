module
public import FRSB.ForwardDerivatives
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section

/-! Every spatial derivative commutes with the genuine Gaussian bridge
average, and relative derivative bounds persist during each heat step. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ContDiff
namespace FRSB

def gaussianScaledAverage (θ b : ℝ) (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  Paper.gaussianExpectation (fun z => F (θ * x + b * z))

theorem iteratedDeriv_gaussianScaledAverage (θ b : ℝ) (F : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (B : ℕ → ℝ) (hb : ∀ j y, ‖iteratedDeriv j F y‖ ≤ B j)
    (j : ℕ) (x : ℝ) :
    iteratedDeriv j (gaussianScaledAverage θ b F) x =
      θ ^ j * Paper.gaussianExpectation (fun z => iteratedDeriv j F (θ * x + b * z)) := by
  induction j generalizing x with
  | zero => simp [iteratedDeriv_zero, gaussianScaledAverage]
  | succ j ih =>
    have hfun : iteratedDeriv j (gaussianScaledAverage θ b F) =
        fun y => θ ^ j * Paper.gaussianExpectation (fun z => iteratedDeriv j F (θ * y + b * z)) := by
      funext y
      exact ih y
    have hd (y : ℝ) : HasDerivAt (iteratedDeriv j F) (iteratedDeriv (j + 1) F y) y := by
      rw [iteratedDeriv_succ]
      exact (hF.differentiable_iteratedDeriv j (by exact_mod_cast WithTop.coe_lt_top j) y).hasDerivAt
    have hi := integrable_gaussian_bounded (fun z => iteratedDeriv j F (θ * x + b * z))
      ((hF.continuous_iteratedDeriv j (by simp)).comp (by fun_prop)) (B j) (fun z => hb j _)
    have hh := Paper.hasDerivAt_gaussian_shift (iteratedDeriv j F) (iteratedDeriv (j + 1) F)
      b (θ * x) (B (j + 1)) (hF.continuous_iteratedDeriv j (by simp))
      (hF.continuous_iteratedDeriv (j + 1) (by simp)) hi hd (hb (j + 1))
    have hout := (hh.comp x ((hasDerivAt_id x).const_mul θ)).const_mul (θ ^ j)
    rw [iteratedDeriv_succ, hfun]
    convert hout.deriv using 1
    · rfl
    · rw [pow_succ]
      ring

/-- Uniform relative bounds survive the heat bridge, with no loss factor. -/
theorem gaussianScaledAverage_relative_derivative_bound (θ b : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1)
    (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (B : ℕ → ℝ)
    (hb : ∀ j y, ‖iteratedDeriv j F y‖ ≤ B j)
    (L : ℝ) (hL : 0 ≤ L) (j : ℕ) (hrel : ∀ y, ‖iteratedDeriv j F y‖ ≤ L * F y)
    (x : ℝ) :
    ‖iteratedDeriv j (gaussianScaledAverage θ b F) x‖ ≤ L * gaussianScaledAverage θ b F x := by
  have hi := integrable_gaussian_bounded (fun z => iteratedDeriv j F (θ * x + b * z))
    ((hF.continuous_iteratedDeriv j (by simp)).comp (by fun_prop)) (B j) (fun z => hb j _)
  have hiF := integrable_gaussian_bounded (fun z => F (θ * x + b * z))
    (hF.continuous.comp (by fun_prop)) (B 0) (fun z => by simpa only [iteratedDeriv_zero] using hb 0 (θ * x + b * z))
  have hbound : ‖Paper.gaussianExpectation (fun z => iteratedDeriv j F (θ * x + b * z))‖ ≤
      L * gaussianScaledAverage θ b F x := by
    unfold Paper.gaussianExpectation gaussianScaledAverage
    calc
      _ ≤ ∫ z, ‖iteratedDeriv j F (θ * x + b * z)‖ ∂gaussianReal 0 1 := norm_integral_le_integral_norm _
      _ ≤ ∫ z, L * F (θ * x + b * z) ∂gaussianReal 0 1 := integral_mono hi.norm (hiF.const_mul L) (fun z => hrel _)
      _ = _ := integral_const_mul _ _
  rw [iteratedDeriv_gaussianScaledAverage θ b F hF B hb j x, norm_mul,
    Real.norm_of_nonneg (pow_nonneg hθ.1 j)]
  have hpow : θ ^ j ≤ 1 := pow_le_one₀ hθ.1 hθ.2
  have hnon : 0 ≤ L * gaussianScaledAverage θ b F x := (norm_nonneg _).trans hbound
  exact (mul_le_mul hpow hbound (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

end FRSB
