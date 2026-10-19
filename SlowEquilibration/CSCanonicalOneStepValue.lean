-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.TwoAtomStationarity

@[expose] public section

/-!
# The genuine ordinary one-step CS value

The entropy integral and full functional are evaluated for the actual
two-atom probability law. The resulting canonical value is an actual
variational minimum; no thermodynamic or ground-state limit is postulated.
-/

namespace SlowEquilibration.TwoAtomStationarity

noncomputable section
open Set MeasureTheory CrisantiSommers CSParisiMeasure

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

theorem integral_inverse {x Q : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hQ : Q ∈ Ioo (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..Q, (xHat (twoAtom x Q) t)⁻¹) =
      Real.log (profileConstant x Q/(1-Q))/x := by
  let C := profileConstant x Q
  have hC : 0 < C := profileConstant_pos hx hQ
  have hcont : ContinuousOn (fun t : ℝ => 1/(C-x*t)) (uIcc (0 : ℝ) Q) := by
    apply continuous_const.continuousOn.div
      (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) Q := by simpa only [uIcc_of_le hQ.1.le] using ht
    exact (profile_affine_pos hx hQ ht'.2).ne'
  have hd : ∀ t ∈ uIcc (0 : ℝ) Q,
      HasDerivAt (fun t : ℝ => -Real.log (C-x*t)/x) (1/(C-x*t)) t := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) Q := by simpa only [uIcc_of_le hQ.1.le] using ht
    have hn : C-x*t ≠ 0 := (profile_affine_pos hx hQ ht'.2).ne'
    have hlin := (hasDerivAt_const t C).sub ((hasDerivAt_id t).const_mul x)
    convert (hlin.log hn).neg.div_const x using 1
    · ext s
      rfl
    · dsimp
      field_simp [hx.1.ne', hn]
      ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable
  have hprofile : (∫ t in (0 : ℝ)..Q, (xHat (twoAtom x Q) t)⁻¹) =
      ∫ t in (0 : ℝ)..Q, 1/(C-x*t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) Q := by simpa only [uIcc_of_le hQ.1.le] using ht
    dsimp only
    rw [xHat_twoAtom ⟨hx.1.le, hx.2.le⟩ ht'.1, ite_eq_left ht'.2]
    simp only [one_div]
    rfl
  rw [hprofile, hi]
  have hCQ : C-x*Q = 1-Q := profile_at_Q x Q
  change -Real.log (C-x*Q)/x-(-Real.log (C-x*0)/x) = Real.log (C/(1-Q))/x
  rw [hCQ, Real.log_div hC.ne' (sub_pos.mpr hQ.2).ne']
  simp only [mul_zero, sub_zero]
  ring

/-- Actual ordinary CS functional at the literal strict two-atom law. -/
theorem functional_twoAtom (μ : FiniteMixture) (β : ℝ) {x Q : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hQ : Q ∈ Ioo (0 : ℝ) 1) :
    functional β μ.xi (twoAtom x Q) Q =
      (β^2*(μ.xi 1-(1-x)*μ.xi Q)+
        Real.log (profileConstant x Q/(1-Q))/x+Real.log (1-Q))/2 := by
  unfold functional
  rw [integral_twoAtom ⟨hx.1.le, hx.2.le⟩, μ.xi_zero, integral_inverse hx hQ]
  simp only [mul_zero, zero_add]

/-- The actual canonical variational value is evaluated from its genuine
two-atom law, with no assumed free-energy formula. -/
theorem variationalValue_of_twoAtom (μ : FiniteMixture) (β : ℝ) {x Q : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hQ : Q ∈ Ioo (0 : ℝ) 1)
    (hlaw : (canonicalMinimizer μ β).law = twoAtom x Q) :
    variationalValue μ β =
      (β^2*(μ.xi 1-(1-x)*μ.xi Q)+
        Real.log (profileConstant x Q/(1-Q))/x+Real.log (1-Q))/2 := by
  have hcut : HasCutoff (canonicalMinimizer μ β).law Q := by
    rw [hlaw]
    exact twoAtom_hasCutoff ⟨hQ.1.le, hQ.2⟩
  rw [variationalValue, (canonicalMinimizer μ β).value_eq β μ.xi hcut, hlaw]
  exact functional_twoAtom μ β hx hQ

end

end SlowEquilibration.TwoAtomStationarity
