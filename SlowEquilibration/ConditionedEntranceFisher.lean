module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.ConditionedEntranceResolventEnergy
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-!
# The entropy/Fisher estimate from the literal resolvent test equation

This is `eq:ent-fisher`: the tangent-line inequality is integrated, equal
masses cancel its linear term, and `F≥1` makes the remaining entropy
nonnegative. The operator-level log-chain rule and test identity remain
explicit inputs, rather than an assumed Fisher conclusion.
-/

namespace SlowEquilibration.ConditionedEntrance
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory
variable {E : Type*} [MeasurableSpace E]

/-- The entropy difference bounds the genuine tested resolvent pairing.
The equal-mass assumption is exactly the conservativeness input. -/
theorem integrated_entropy_tangent_line (μ : Measure E) (F₀ F : E → ℝ)
    (h₀ : ∀ᵐ x ∂μ, 0 < F₀ x) (h : ∀ᵐ x ∂μ, 0 < F x)
    (hi₀ : Integrable F₀ μ) (hi : Integrable F μ)
    (he₀ : Integrable (fun x => F₀ x * Real.log (F₀ x)) μ)
    (he : Integrable (fun x => F x * Real.log (F x)) μ)
    (ht : Integrable (fun x => (F₀ x - F x) * Real.log (F x)) μ)
    (hmass : (∫ x, F₀ x ∂μ) = ∫ x, F x ∂μ) :
    (∫ x, (F₀ x - F x) * Real.log (F x) ∂μ) ≤
      (∫ x, F₀ x * Real.log (F₀ x) ∂μ) - ∫ x, F x * Real.log (F x) ∂μ := by
  have hlin := integral_mono_ae ht ((he₀.sub he).sub (hi₀.sub hi))
    (by filter_upwards [h₀, h] with x h₀x hx using entropy_tangent_line h₀x hx)
  dsimp only [Pi.sub_apply] at hlin
  have hsub := integral_sub (he₀.sub he) (hi₀.sub hi)
  change (∫ x, F₀ x * Real.log (F₀ x) - F x * Real.log (F x) - (F₀ x - F x) ∂μ) =
    (∫ x, F₀ x * Real.log (F₀ x) - F x * Real.log (F x) ∂μ) -
      (∫ x, F₀ x - F x ∂μ) at hsub
  have hsub₀ := integral_sub he₀ he
  change (∫ x, F₀ x * Real.log (F₀ x) - F x * Real.log (F x) ∂μ) =
    (∫ x, F₀ x * Real.log (F₀ x) ∂μ) - (∫ x, F x * Real.log (F x) ∂μ) at hsub₀
  have hsub₁ := integral_sub hi₀ hi
  change (∫ x, F₀ x - F x ∂μ) = (∫ x, F₀ x ∂μ) - (∫ x, F x ∂μ) at hsub₁
  rw [hsub, hsub₀, hsub₁, hmass, sub_self, sub_zero] at hlin
  exact hlin

/-- The actual Fisher bound follows from the tested equation, without a
spectral gap or a perturbation-size factor. -/
theorem fisher_bound_of_resolvent_test (μ : Measure E) (F₀ F : E → ℝ)
    {lam J : ℝ} (hlam : 0 ≤ lam)
    (h₀ : ∀ᵐ x ∂μ, 0 < F₀ x) (h : ∀ᵐ x ∂μ, 1 ≤ F x)
    (hi₀ : Integrable F₀ μ) (hi : Integrable F μ)
    (he₀ : Integrable (fun x => F₀ x * Real.log (F₀ x)) μ)
    (he : Integrable (fun x => F x * Real.log (F x)) μ)
    (ht : Integrable (fun x => (F₀ x - F x) * Real.log (F x)) μ)
    (hmass : (∫ x, F₀ x ∂μ) = ∫ x, F x ∂μ)
    (htest : J = lam * ∫ x, (F₀ x - F x) * Real.log (F x) ∂μ) :
    J ≤ lam * ∫ x, F₀ x * Real.log (F₀ x) ∂μ := by
  have hp : ∀ᵐ x ∂μ, 0 < F x := h.mono fun _ hx => lt_of_lt_of_le (by norm_num) hx
  have hepos : 0 ≤ ∫ x, F x * Real.log (F x) ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [h] with x hx
    exact mul_nonneg (by linarith) (Real.log_nonneg hx)
  have hec := integrated_entropy_tangent_line μ F₀ F h₀ hp hi₀ hi he₀ he ht hmass
  rw [htest]
  exact mul_le_mul_of_nonneg_left (hec.trans (sub_le_self _ hepos)) hlam

end
end SlowEquilibration.ConditionedEntrance
