-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.InfiniteMixtureFiniteCutoff
public import SlowEquilibration.MixtureThresholds

/-! Actual static-threshold monotonicity under the nonnegative source cutoff.
This keeps every fixed subcritical temperature valid for all nonzero cutoffs. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.InfiniteMixture
open Set

theorem staticThreshold_le_finiteCutoff (μ : InfiniteMixture) (P : ℕ)
    (hP : ∃ p,p≤P ∧ 0<μ.coeff p) :
    Thresholds.staticThreshold μ.xi≤Thresholds.staticThreshold (finiteCutoff μ P hP).xi := by
  apply Real.sqrt_le_sqrt
  have hb : BddBelow (Thresholds.staticRatio μ.xi '' Ioo 0 1) := by
    refine ⟨0,?_⟩
    rintro _ ⟨r,hr,rfl⟩
    exact div_nonneg (Thresholds.staticNumerator_pos hr).le (μ.xi_pos hr).le
  apply le_csInf
  · exact ⟨Thresholds.staticRatio (finiteCutoff μ P hP).xi (1/2),1/2,by norm_num,rfl⟩
  · rintro _ ⟨r,hr,rfl⟩
    apply (csInf_le hb ⟨r,hr,rfl⟩).trans
    exact div_le_div_of_nonneg_left (Thresholds.staticNumerator_pos hr).le
      ((finiteCutoff μ P hP).xi_pos hr.1) (μ.finiteCutoff_xi_le P hP ⟨hr.1.le,hr.2.le⟩)

theorem Phi_finiteCutoff_le (μ : InfiniteMixture) (P : ℕ)
    (hP : ∃ p,p≤P ∧ 0<μ.coeff p) (β : ℝ) {r : ℝ} (hr : r∈Icc 0 1) :
    Thresholds.Phi (finiteCutoff μ P hP).xi β r≤Thresholds.Phi μ.xi β r := by
  unfold Thresholds.Phi
  have h := mul_le_mul_of_nonneg_left (μ.finiteCutoff_xi_le P hP hr) (sq_nonneg β)
  linarith

end SlowEquilibration.InfiniteMixture
