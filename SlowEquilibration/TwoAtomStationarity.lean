-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSPureModels
public import SlowEquilibration.PureScalarStatic

@[expose] public section

/-!
# Genuine two-atom entropy integrals and contact stationarity

The ordinary hatted profile of the literal probability law is integrated
analytically. Contact equations are consequences of the actual contact value
and derivative; later canonical applications discharge these from optimality.
-/

namespace SlowEquilibration.TwoAtomStationarity

noncomputable section
open MeasureTheory Set CrisantiSommers

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

def profileConstant (x Q : ℝ) : ℝ := 1-Q+x*Q

theorem profileConstant_pos {x Q : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hQ : Q ∈ Ioo (0 : ℝ) 1) : 0 < profileConstant x Q := by
  have hmul := mul_pos hx.1 hQ.1
  unfold profileConstant
  linarith [hQ.2]

theorem profile_affine_pos {x Q t : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hQ : Q ∈ Ioo (0 : ℝ) 1) (ht : t ≤ Q) :
    0 < profileConstant x Q-x*t := by
  have hmul := mul_le_mul_of_nonneg_left ht hx.1.le
  unfold profileConstant
  linarith [hQ.2]

theorem profile_at_Q (x Q : ℝ) : profileConstant x Q-x*Q = 1-Q := by
  unfold profileConstant
  ring

/-- Exact ordinary entropy derivative integral of the actual two-atom law. -/
theorem integral_inverseSquare {x Q : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hQ : Q ∈ Ioo (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..Q, 1/(xHat (twoAtom x Q) t)^2) =
      Q/(profileConstant x Q*(1-Q)) := by
  let C := profileConstant x Q
  have hC : 0 < C := profileConstant_pos hx hQ
  have hcont : ContinuousOn (fun t : ℝ => 1/(C-x*t)^2) (uIcc (0 : ℝ) Q) := by
    apply continuous_const.continuousOn.div
      ((continuous_const.sub (continuous_const.mul continuous_id)).continuousOn.pow 2)
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) Q := by simpa only [uIcc_of_le hQ.1.le] using ht
    exact pow_ne_zero 2 (profile_affine_pos hx hQ ht'.2).ne'
  have hd : ∀ t ∈ uIcc (0 : ℝ) Q,
      HasDerivAt (fun t : ℝ => t/(C*(C-x*t))) (1/(C-x*t)^2) t := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) Q := by simpa only [uIcc_of_le hQ.1.le] using ht
    have hn : C-x*t ≠ 0 := (profile_affine_pos hx hQ ht'.2).ne'
    have hlin := (hasDerivAt_const t C).sub ((hasDerivAt_id t).const_mul x)
    convert (hasDerivAt_id t).div (hlin.const_mul C) (mul_ne_zero hC.ne' hn) using 1
    · ext s
      rfl
    · dsimp
      field_simp [hC.ne', hn]
      ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable
  have hprofile : (∫ t in (0 : ℝ)..Q, 1/(xHat (twoAtom x Q) t)^2) =
      ∫ t in (0 : ℝ)..Q, 1/(C-x*t)^2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) Q := by simpa only [uIcc_of_le hQ.1.le] using ht
    dsimp only
    rw [xHat_twoAtom ⟨hx.1.le, hx.2.le⟩ ht'.1, ite_eq_left ht'.2]
    rfl
  rw [hprofile]
  have hCQ : C-x*Q = 1-Q := profile_at_Q x Q
  simpa only [hCQ, zero_div, sub_zero] using hi

/-- Exact ordinary triangular entropy integral of the actual two-atom law. -/
theorem integral_triangular {x Q : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hQ : Q ∈ Ioo (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..Q, (Q-t)/(xHat (twoAtom x Q) t)^2) =
      (Real.log (profileConstant x Q/(1-Q))-x*Q/profileConstant x Q)/x^2 := by
  let C := profileConstant x Q
  have hC : 0 < C := profileConstant_pos hx hQ
  have hcont : ContinuousOn (fun t : ℝ => (Q-t)/(C-x*t)^2) (uIcc (0 : ℝ) Q) := by
    apply (continuous_const.sub continuous_id).continuousOn.div
      ((continuous_const.sub (continuous_const.mul continuous_id)).continuousOn.pow 2)
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) Q := by simpa only [uIcc_of_le hQ.1.le] using ht
    exact pow_ne_zero 2 (profile_affine_pos hx hQ ht'.2).ne'
  have hd : ∀ t ∈ uIcc (0 : ℝ) Q,
      HasDerivAt (fun t : ℝ => (x*Q-C)/(x^2*(C-x*t))-Real.log (C-x*t)/x^2)
        ((Q-t)/(C-x*t)^2) t := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) Q := by simpa only [uIcc_of_le hQ.1.le] using ht
    have hn : C-x*t ≠ 0 := (profile_affine_pos hx hQ ht'.2).ne'
    have hlin := (hasDerivAt_const t C).sub ((hasDerivAt_id t).const_mul x)
    have hquot := (hasDerivAt_const t (x*Q-C)).div (hlin.const_mul (x^2))
      (mul_ne_zero (pow_ne_zero 2 hx.1.ne') hn)
    convert hquot.sub ((hlin.log hn).div_const (x^2)) using 1
    · ext s
      rfl
    · dsimp
      field_simp [hx.1.ne', hn]
      ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable
  have hprofile : (∫ t in (0 : ℝ)..Q, (Q-t)/(xHat (twoAtom x Q) t)^2) =
      ∫ t in (0 : ℝ)..Q, (Q-t)/(C-x*t)^2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) Q := by simpa only [uIcc_of_le hQ.1.le] using ht
    dsimp only
    rw [xHat_twoAtom ⟨hx.1.le, hx.2.le⟩ ht'.1, ite_eq_left ht'.2]
    rfl
  rw [hprofile, hi]
  change (x*Q-C)/(x^2*(C-x*Q))-Real.log (C-x*Q)/x^2-
    ((x*Q-C)/(x^2*(C-x*0))-Real.log (C-x*0)/x^2) =
      (Real.log (C/(1-Q))-x*Q/C)/x^2
  have hCQ : C-x*Q = 1-Q := profile_at_Q x Q
  rw [hCQ, Real.log_div hC.ne' (sub_pos.mpr hQ.2).ne']
  simp only [mul_zero, sub_zero]
  field_simp [hx.1.ne', hC.ne', (sub_pos.mpr hQ.2).ne']
  dsimp [C, profileConstant]
  ring

/-- Ordinary two-atom contact stationarity is deduced from the actual
contact value and actual derivative; both entropy integrals are proved. -/
theorem contact_equations (μ : FiniteMixture) (β : ℝ) {x Q : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hQ : Q ∈ Ioo (0 : ℝ) 1)
    (hvalue : CSStructure.potential μ β (twoAtom x Q) Q = 0)
    (hderiv : deriv (CSStructure.potential μ β (twoAtom x Q)) Q = 0) :
    β^2*μ.xi1 Q = Q/(profileConstant x Q*(1-Q)) ∧
      β^2*μ.xi Q = (Real.log (profileConstant x Q/(1-Q))-
        x*Q/profileConstant x Q)/x^2 := by
  have : IsProbabilityMeasure (twoAtom x Q) := twoAtom_probability ⟨hx.1.le, hx.2.le⟩
  have hcut := twoAtom_hasCutoff (x := x) ⟨hQ.1.le, hQ.2⟩
  constructor
  · rw [(CSStructure.potential_hasDerivAt μ β (twoAtom x Q) hcut hQ.2).deriv,
      integral_inverseSquare hx hQ] at hderiv
    linarith
  · unfold CSStructure.potential firstVariation at hvalue
    rw [integral_triangular hx hQ] at hvalue
    linarith

end

end SlowEquilibration.TwoAtomStationarity
