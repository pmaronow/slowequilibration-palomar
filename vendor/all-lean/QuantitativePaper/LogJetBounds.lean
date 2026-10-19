module
public import QuantitativePaper.ExponentialJetBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

/-! Uniform higher logarithmic derivative bounds from relative partition
derivative bounds. Normalizing at the evaluation point keeps the logarithm's
derivatives at the fixed positive scalar 1. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ContDiff
namespace QuantitativePaper
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def logJetCoefficient (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j+1),‖iteratedFDerivWithin ℝ i Real.log ({0}ᶜ : Set ℝ) 1‖

theorem logJetCoefficient_nonneg (j : ℕ) : 0 ≤ logJetCoefficient j := by
  unfold logJetCoefficient
  positivity

theorem norm_iteratedFDeriv_log_le_of_relative {N j : ℕ} (f : E → ℝ)
    (hf : ContDiff ℝ N f) (hpos : ∀ y,0 < f y) (hj0 : 1 ≤ j) (hj : j ≤ N)
    (K : ℝ) (x : E)
    (hrelative : ∀ i,1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i f x‖ ≤ K^i*f x) :
    ‖iteratedFDeriv ℝ j (fun y => Real.log (f y)) x‖ ≤
      (j.factorial : ℝ)*logJetCoefficient j*K^j := by
  let h := fun y => (f x)⁻¹*f y
  have hh : ContDiff ℝ N h := contDiff_const.mul hf
  have hx : h x = 1 := inv_mul_cancel₀ (hpos x).ne'
  have hr : range h ⊆ ({0}ᶜ : Set ℝ) := by
    rintro _ ⟨y,rfl⟩
    exact (mul_pos (inv_pos.mpr (hpos x)) (hpos y)).ne'
  have hC (i : ℕ) (hi : i ≤ j) :
      ‖iteratedFDerivWithin ℝ i Real.log ({0}ᶜ : Set ℝ) (h x)‖ ≤ logJetCoefficient j := by
    rw [hx]
    unfold logJetCoefficient
    exact Finset.single_le_sum
      (f := fun i => ‖iteratedFDerivWithin ℝ i Real.log ({0}ᶜ : Set ℝ) 1‖) (fun i _ => norm_nonneg _)
      (Finset.mem_range.mpr (by omega))
  have hD (i : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) :
      ‖iteratedFDeriv ℝ i h x‖ ≤ K^i := by
    have hfi : ContDiffAt ℝ i f x := (hf.of_le (by norm_cast;omega)).contDiffAt
    have he : iteratedFDeriv ℝ i h x = (f x)⁻¹ • iteratedFDeriv ℝ i f x :=
      by simpa only [h,smul_eq_mul] using iteratedFDeriv_const_smul_apply' (a := (f x)⁻¹) hfi
    rw [he,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (hpos x)]
    apply (inv_mul_le_iff₀ (hpos x)).mpr
    simpa only [mul_comm] using hrelative i hi hij
  have hb := norm_iteratedFDeriv_comp_le' hr isOpen_compl_singleton.uniqueDiffOn
    Real.contDiffOn_log hh (by norm_cast) x hC hD
  have he : (fun y => Real.log (f y)) = fun y => Real.log (h y)+Real.log (f x) := by
    funext y
    unfold h
    rw [Real.log_mul (inv_ne_zero (hpos x).ne') (hpos y).ne',Real.log_inv]
    ring
  rw [he]
  change ‖iteratedFDeriv ℝ j ((Real.log ∘ h)+(fun _ => Real.log (f x))) x‖ ≤ _
  rw [iteratedFDeriv_add_apply]
  · rw [iteratedFDeriv_const_of_ne (by omega),Pi.zero_apply,add_zero]
    exact hb
  · exact ((hh.of_le (by norm_cast)).log (fun y => (mul_pos (inv_pos.mpr (hpos x)) (hpos y)).ne')).contDiffAt
  · exact contDiffAt_const

end QuantitativePaper
