module
public import QuantitativePaper.SmoothIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

@[expose] public section

/-! Domination of actual higher derivatives of an exponential, used in the
finite vector Gaussian smoothing. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff
namespace QuantitativePaper
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedFDeriv_exp_mul_le {N j : ℕ} (f : E → ℝ) (hf : ContDiff ℝ N f)
    (hj : j ≤ N) (m D : ℝ) (x : E)
    (hD : ∀ i,1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i f x‖ ≤ D^i) :
    ‖iteratedFDeriv ℝ j (fun y => Real.exp (m*f y)) x‖ ≤
      (j.factorial : ℝ)*(max 1 |m|)^j*Real.exp (m*f x)*D^j := by
  let g := fun r : ℝ => Real.exp (m*r)
  have hg : ContDiff ℝ N g := (contDiff_const.mul contDiff_id).exp
  have hC (i : ℕ) (hi : i ≤ j) : ‖iteratedFDeriv ℝ i g (f x)‖ ≤
      (max 1 |m|)^j*Real.exp (m*f x) := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    change ‖iteratedDeriv i (fun r => Real.exp (m*r)) (f x)‖ ≤ _
    rw [iteratedDeriv_exp_const_mul]
    simp only [Real.norm_eq_abs,abs_mul,abs_pow,abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact (pow_le_pow_left₀ (abs_nonneg _) (le_max_right _ _) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) hi)
  have hh := norm_iteratedFDeriv_comp_le hg hf (by norm_cast) x hC hD
  simpa only [g,Function.comp_def,mul_assoc] using hh

end QuantitativePaper
