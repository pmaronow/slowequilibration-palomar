module
-- SPDX-License-Identifier: Apache-2.0

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

@[expose] public section

/-! Cauchy–Schwarz against the actual tilted measure, in a form directly
suited to the two commutator errors in `eq:ent-energy-errors`. -/

namespace SlowEquilibration.ConditionedEntrance
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace

variable {E V : Type*} [MeasurableSpace E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The norm of the actual L² class is the square root of its genuine
Bochner integral, with the representative identified almost everywhere. -/
lemma norm_toLp_sq_eq_integral (μ : Measure E) (X : E → V) (hX : MemLp X 2 μ) :
    ‖hX.toLp X‖ ^ 2 = ∫ x, ‖X x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hX.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

/-- Actual integral Cauchy–Schwarz, including vector-valued gradient fields.
Only square-integrability is assumed; no energy-error estimate is supplied. -/
theorem integral_inner_abs_le_sqrt (μ : Measure E) (X Y : E → V)
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ)
    (hX₂ : Integrable (fun x => ‖X x‖ ^ 2) μ)
    (hY₂ : Integrable (fun x => ‖Y x‖ ^ 2) μ) :
    |∫ x, inner ℝ (X x) (Y x) ∂μ| ≤
      Real.sqrt ((∫ x, ‖X x‖ ^ 2 ∂μ) * ∫ x, ‖Y x‖ ^ 2 ∂μ) := by
  have hmX : MemLp X 2 μ := (memLp_two_iff_integrable_sq_norm hX).2 hX₂
  have hmY : MemLp Y 2 μ := (memLp_two_iff_integrable_sq_norm hY).2 hY₂
  have hi : inner ℝ (hmX.toLp X) (hmY.toLp Y) =
      ∫ x, inner ℝ (X x) (Y x) ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hmX.coeFn_toLp, hmY.coeFn_toLp] with x hx hy
    rw [hx, hy]
  have hn := norm_inner_le_norm (𝕜 := ℝ) (hmX.toLp X) (hmY.toLp Y)
  rw [Real.norm_eq_abs, hi] at hn
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hn 2
  rw [mul_pow, norm_toLp_sq_eq_integral μ X hmX,
    norm_toLp_sq_eq_integral μ Y hmY] at hsq
  have hpX : 0 ≤ ∫ x, ‖X x‖ ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hpY : 0 ≤ ∫ x, ‖Y x‖ ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hp := mul_nonneg hpX hpY
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).1
  rw [Real.sq_sqrt hp]
  exact hsq

/-- Cauchy–Schwarz followed by genuine small-moment and weighted-energy
bounds. This is the exact numerical form used for the gradient commutator. -/
theorem integral_inner_abs_le_sqrt_of_moments (μ : Measure E) (X Y : E → V)
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ)
    (hX₂ : Integrable (fun x => ‖X x‖ ^ 2) μ)
    (hY₂ : Integrable (fun x => ‖Y x‖ ^ 2) μ) {ε J B : ℝ}
    (hε : 0 ≤ ε) (hJ : 0 ≤ J) (_hB : 0 ≤ B)
    (hsmall : (∫ x, ‖X x‖ ^ 2 ∂μ) ≤ 2 * ε * J)
    (henergy : (∫ x, ‖Y x‖ ^ 2 ∂μ) ≤ B) :
    |∫ x, inner ℝ (X x) (Y x) ∂μ| ≤ Real.sqrt (2 * ε * J * B) := by
  apply (integral_inner_abs_le_sqrt μ X Y hX hY hX₂ hY₂).trans
  apply Real.sqrt_le_sqrt
  exact mul_le_mul hsmall henergy (integral_nonneg fun x => sq_nonneg _)
    (by positivity)

end
end SlowEquilibration.ConditionedEntrance
