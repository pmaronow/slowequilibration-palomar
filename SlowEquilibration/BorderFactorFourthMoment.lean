-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.BorderMomentTransfer

/-! Fourth moments of the literal border factor from ordinary corner
fourth and row eighth moments. All integrability is proved on the same space.
-/
@[expose] public section
namespace SlowEquilibration.BorderFactorFourthMoment
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure Ω}

def factor (k ρ : ℝ) (a : Ω → ℝ) (u : Ω → E) (x : Ω) : ℝ :=
  |k - a x| + ‖u x‖ ^ 2 / ρ

lemma factor_nonneg (k : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (a : Ω → ℝ) (u : Ω → E) (x : Ω) :
    0 ≤ factor k ρ a u x := add_nonneg (abs_nonneg _) (div_nonneg (sq_nonneg _) hρ.le)

lemma factor_measurable (k ρ : ℝ) {a : Ω → ℝ} {u : Ω → E}
    (ha : Measurable a) (hu : Measurable u) : Measurable (factor k ρ a u) :=
  (measurable_const.sub ha).abs.add ((hu.norm.pow_const 2).div_const ρ)

lemma factor_fourth_bound (k a : ℝ) (u : E) {ρ L : ℝ}
    (hρ : 0 < ρ) (hL : ρ⁻¹ ≤ L) :
    (|k - a| + ‖u‖ ^ 2 / ρ) ^ 4 ≤
      64 * (|k| ^ 4 + |a| ^ 4) + 8 * L ^ 4 * ‖u‖ ^ 8 := by
  have ha : |k - a| ^ 4 ≤ 8 * (|k| ^ 4 + |a| ^ 4) := by
    have hp := pow_le_pow_left₀ (abs_nonneg (k - a)) (abs_sub k a) 4
    have hAdd := add_pow_le (abs_nonneg k) (abs_nonneg a) 4
    norm_num at hAdd
    exact hp.trans hAdd
  have hu : (‖u‖ ^ 2 / ρ) ^ 4 ≤ L ^ 4 * ‖u‖ ^ 8 := by
    have hLp := pow_le_pow_left₀ (inv_nonneg.mpr hρ.le) hL 4
    calc
      _ = ρ⁻¹ ^ 4 * ‖u‖ ^ 8 := by rw [div_eq_mul_inv, mul_pow, ← pow_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hLp (pow_nonneg (norm_nonneg _) _)
  have hs := add_pow_le (abs_nonneg (k - a)) (div_nonneg (sq_nonneg ‖u‖) hρ.le) 4
  norm_num only at hs
  nlinarith

/-- Primitive ordinary moments imply the literal border-factor fourth
moment and its integrability. No independence is required. -/
theorem factor_fourth_moment [IsProbabilityMeasure μ]
    (k : ℝ) {ρ L Ca Cu : ℝ} (hρ : 0 < ρ) (hL : ρ⁻¹ ≤ L)
    (a : Ω → ℝ) (u : Ω → E) (ha : Measurable a) (hu : Measurable u)
    (haI : Integrable (fun x => |a x| ^ 4) μ) (huI : Integrable (fun x => ‖u x‖ ^ 8) μ)
    (haM : (∫ x, |a x| ^ 4 ∂μ) ≤ Ca) (huM : (∫ x, ‖u x‖ ^ 8 ∂μ) ≤ Cu) :
    Integrable (fun x => factor k ρ a u x ^ 4) μ ∧
      (∫ x, factor k ρ a u x ^ 4 ∂μ) ≤
        64 * (|k| ^ 4 + Ca) + 8 * L ^ 4 * Cu := by
  have hmajor : Integrable (fun x => 64 * (|k| ^ 4 + |a x| ^ 4) +
      8 * L ^ 4 * ‖u x‖ ^ 8) μ :=
    ((integrable_const (|k| ^ 4)).add haI).const_mul 64 |>.add (huI.const_mul (8 * L ^ 4))
  have hp (x) : factor k ρ a u x ^ 4 ≤
      64 * (|k| ^ 4 + |a x| ^ 4) + 8 * L ^ 4 * ‖u x‖ ^ 8 :=
    factor_fourth_bound k (a x) (u x) hρ hL
  have hi : Integrable (fun x => factor k ρ a u x ^ 4) μ :=
    hmajor.mono' ((factor_measurable k ρ ha hu).pow_const 4).aestronglyMeasurable
      (ae_of_all μ (fun x => by rw [Real.norm_of_nonneg (pow_nonneg (factor_nonneg k hρ a u x) _)]; exact hp x))
  refine ⟨hi, (integral_mono hi hmajor hp).trans ?_⟩
  have hsum := integral_add
    (((integrable_const (|k| ^ 4)).add haI).const_mul 64) (huI.const_mul (8 * L ^ 4))
  simp only [Pi.add_apply] at hsum
  rw [hsum, integral_const_mul, integral_const_mul]
  have hadd := integral_add (integrable_const (|k| ^ 4)) haI
  rw [hadd, integral_const, probReal_univ, one_smul]
  exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl haM) (by norm_num))
    (mul_le_mul_of_nonneg_left huM (by positivity))

end
end SlowEquilibration.BorderFactorFourthMoment
