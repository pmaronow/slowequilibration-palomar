-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEClippedResolventConvergence

/-! Dimension-free shift continuity of the actual clipped normalized GOE
resolvent, valid pointwise for every matrix and every real shift. -/
@[expose] public section
namespace SlowEquilibration.GOEClippedResolvent
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set GOEAsymptotics
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

lemma abs_max_sub_max_le (ρ a b : ℝ) : |max ρ a-max ρ b| ≤ |a-b| := by
  by_cases ha : ρ ≤ a <;> by_cases hb : ρ ≤ b
  · rw [max_eq_right ha,max_eq_right hb]
  · rw [max_eq_right ha,max_eq_left (le_of_not_ge hb),abs_of_nonneg (sub_nonneg.mpr ha),
      abs_of_nonneg (sub_nonneg.mpr (le_trans (le_of_not_ge hb) ha))]
    linarith
  · rw [max_eq_left (le_of_not_ge ha),max_eq_right hb,abs_of_nonpos (sub_nonpos.mpr hb),
      abs_of_nonpos (sub_nonpos.mpr (le_trans (le_of_not_ge ha) hb))]
    linarith
  · rw [max_eq_left (le_of_not_ge ha),max_eq_left (le_of_not_ge hb),sub_self,abs_zero]
    exact abs_nonneg _

lemma clipped_inverse_lipschitz {ρ : ℝ} (hρ : 0 < ρ) (a b : ℝ) :
    |(max ρ a)⁻¹-(max ρ b)⁻¹| ≤ |a-b|/ρ^2 := by
  have hA : 0 < max ρ a:=hρ.trans_le (le_max_left _ _)
  have hB : 0 < max ρ b:=hρ.trans_le (le_max_left _ _)
  rw [inv_sub_inv hA.ne' hB.ne',abs_div,abs_mul,abs_of_pos hA,abs_of_pos hB]
  have hmax:=abs_max_sub_max_le ρ a b
  rw [abs_sub_comm] at hmax
  calc
    _ ≤ |a-b|/(max ρ a*max ρ b) := div_le_div_of_nonneg_right hmax (mul_pos hA hB).le
    _ ≤ |a-b|/ρ^2 := div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hρ)
      (by simpa only [pow_two] using mul_le_mul (le_max_left ρ a) (le_max_left ρ b) hρ.le hA.le)

/-- The true normalized finite trace is Lipschitz uniformly in matrix
dimension and matrix realization. -/
theorem clippedResolvent_shift_bound (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (s t : ℝ)
    (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    |clippedResolvent n s ρ W-clippedResolvent n t ρ W| ≤ |s-t|/ρ^2 := by
  unfold clippedResolvent
  rw [← sub_div,abs_div,abs_of_pos (by positivity : 0 < (n+1:ℝ)),← Finset.sum_sub_distrib]
  apply (div_le_iff₀ (by positivity : 0 < (n+1:ℝ))).mpr
  calc
    _ ≤ ∑ i : Fin (n+1),|(max ρ (2+s-eigenvalues n W i))⁻¹-(max ρ (2+t-eigenvalues n W i))⁻¹| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (n+1),|s-t|/ρ^2 := Finset.sum_le_sum (fun i _=>by
      have h:=clipped_inverse_lipschitz hρ (2+s-eigenvalues n W i) (2+t-eigenvalues n W i)
      convert h using 1
      congr 2
      ring)
    _=_ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one];ring

end
end SlowEquilibration.GOEClippedResolvent
