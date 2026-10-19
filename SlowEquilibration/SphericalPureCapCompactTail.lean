-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureCapEndpointIntegral
public import SlowEquilibration.SphericalPureLaplaceRegularity

@[expose] public section

/-! Uniform integral bounds for compact pure latitude regions away from the
contact. Combine with the cap exponent gap on the two exterior intervals. -/

namespace SlowEquilibration.SphericalPureCapCompactTail
noncomputable section
open Set MeasureTheory
open SphericalTAPCriticalPureLatitudeProfile
open SphericalPureLaplaceRegularity
set_option autoImplicit false

/-- A fixed exponent gap on a compact physical latitude interval produces an
exponentially small integral, uniformly under bounded critical-value shifts. -/
theorem sourcePure_cap_compact_tail
    (p : ℕ) {β Q E l r m δ L : ℝ}
    (hQ : 0 < Q) (hβ : 0 < β) (hL : 0 ≤ L)
    (hlr : l ≤ r)
    (hband : Icc l r ⊆ Ioo (-1:ℝ) 1)
    (hband01 : Icc l r ⊆ Icc (0:ℝ) 1)
    (hgap : ∀ t ∈ Icc l r,
      sourcePureLatitudeExponent p 1 Q β E t ≤
        sourcePureLatitudeExponent p 1 Q β E m-δ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ N : ℕ, ∀ u : ℝ, u ≤ L →
      (∫ t in l..r, sourcePureLatitudeJacobian t *
        Real.exp ((N:ℝ)*sourcePureLatitudeExponent p 1 Q β E t+
          β*u*t^p)) ≤
        (r-l)*M*Real.exp ((N:ℝ)*
          (sourcePureLatitudeExponent p 1 Q β E m-δ)+β*L) := by
  obtain ⟨M,hM,hamp⟩ := sourcePureLatitudeJacobian_bounded_on_band hband
  refine ⟨M,hM,?_⟩
  intro N u hu
  let φ := sourcePureLatitudeExponent p 1 Q β E
  have hφcont : ContinuousOn φ (Icc l r) :=
    ((sourcePureLatitudeExponent_contDiffOn p 1 Q β E hQ).mono hband).continuousOn
  have hJcont : ContinuousOn sourcePureLatitudeJacobian (Icc l r) := by
    intro t ht
    exact (sourcePureLatitudeJacobian_continuousAt (hband ht)).continuousWithinAt
  have hcont : ContinuousOn (fun t : ℝ => sourcePureLatitudeJacobian t *
      Real.exp ((N:ℝ)*φ t+β*u*t^p)) (Icc l r) := by
    have hpert : Continuous (fun t : ℝ => β*u*t^p) := by fun_prop
    exact hJcont.mul (Real.continuous_exp.comp_continuousOn
      ((continuous_const.continuousOn.mul hφcont).add hpert.continuousOn))
  have hint : IntervalIntegrable (fun t : ℝ => sourcePureLatitudeJacobian t *
      Real.exp ((N:ℝ)*φ t+β*u*t^p)) volume l r :=
    hcont.intervalIntegrable_of_Icc hlr
  have hpt : ∀ t ∈ Icc l r,
      sourcePureLatitudeJacobian t *
        Real.exp ((N:ℝ)*φ t+β*u*t^p) ≤
          M*Real.exp ((N:ℝ)*(φ m-δ)+β*L) := by
    intro t ht
    have ht01 := hband01 ht
    have htp0 : 0 ≤ t^p := pow_nonneg ht01.1 _
    have htp1 : t^p ≤ 1 := pow_le_one₀ ht01.1 ht01.2
    have huBound : β*u*t^p ≤ β*L := by
      by_cases hu0 : 0 ≤ u
      · have hmul : β*u*t^p ≤ β*u := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left htp1 (mul_nonneg hβ.le hu0)
        nlinarith [mul_le_mul_of_nonneg_left hu hβ.le]
      · have hneg : β*u*t^p ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos hβ.le (le_of_not_ge hu0)) htp0
        nlinarith [mul_nonneg hβ.le hL]
    have hNr : (0:ℝ) ≤ N := by positivity
    have hφ := hgap t ht
    have hExp : Real.exp ((N:ℝ)*φ t+β*u*t^p) ≤
        Real.exp ((N:ℝ)*(φ m-δ)+β*L) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hφ hNr]
    have hJ : sourcePureLatitudeJacobian t ≤ M :=
      (le_abs_self _).trans (hamp t ht)
    exact mul_le_mul hJ hExp (Real.exp_pos _).le hM
  have hi := intervalIntegral.integral_mono_on hlr hint intervalIntegrable_const hpt
  calc
    _ ≤ ∫ t in l..r, M*Real.exp ((N:ℝ)*(φ m-δ)+β*L) := hi
    _ = (r-l)*M*Real.exp ((N:ℝ)*(φ m-δ)+β*L) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring

end
end SlowEquilibration.SphericalPureCapCompactTail
