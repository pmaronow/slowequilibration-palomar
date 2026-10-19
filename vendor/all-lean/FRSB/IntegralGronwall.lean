module
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-! Integral Gronwall with continuous nonnegative state error and a total forcing budget. -/
noncomputable section
open Set MeasureTheory
namespace FRSB

/-- A continuous nonnegative path error satisfying the genuine integral
inequality is bounded by the explicit exponential Gronwall factor. -/
theorem integral_gronwall_exp_bound (e : ℝ → ℝ) (he : Continuous e)
    (D K : ℝ) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (henon : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ e t)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, e t ≤ D + K * ∫ s in 0..t, e s) :
    ∀ t ∈ Icc (0 : ℝ) 1, e t ≤ D * Real.exp K := by
  let f : ℝ → ℝ := fun t => D + K * ∫ s in 0..t, e s
  have hfder (t : ℝ) : HasDerivAt f (K * e t) t :=
    ((intervalIntegral.integral_hasDerivAt_right (he.intervalIntegrable 0 t)
      (he.stronglyMeasurableAtFilter volume (nhds t)) he.continuousAt).const_mul K).const_add D
  have hf : Continuous f := continuous_iff_continuousAt.mpr fun t => (hfder t).continuousAt
  have hf0 : ‖f 0‖ ≤ D := by simp [f, Real.norm_eq_abs, abs_of_nonneg hD]
  have hb (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : ‖K * e t‖ ≤ K * ‖f t‖ + 0 := by
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK (henon t ht')), add_zero]
    exact (mul_le_mul_of_nonneg_left (hbound t ht') hK).trans
      (mul_le_mul_of_nonneg_left (le_abs_self _) hK)
  intro t ht
  have hn := norm_le_gronwallBound_of_norm_deriv_right_le hf.continuousOn
    (fun r _ => (hfder r).hasDerivWithinAt) hf0 hb t ht
  rw [gronwallBound_ε0, sub_zero] at hn
  exact (hbound t ht).trans ((le_abs_self _).trans (hn.trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [ht.2])) hD)))

end FRSB
