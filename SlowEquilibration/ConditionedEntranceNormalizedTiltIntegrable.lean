-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceTiltCommutator

/-! Integrability transfer for the literal globally normalized Gibbs tilt.
This allows weighted reference and gradient square moments proved under the
base product law to serve as actual L¹ inputs to energy absorption. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false

theorem integrable_normalizedTilt_iff
    {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (w f : E → ℝ) (hw : Measurable w) {M : ℝ} (hM : 0 < M) :
    Integrable f (normalizedTilt μ w M) ↔
      Integrable (fun x => Real.exp (w x) * f x) μ := by
  have hden : Measurable (fun x => ENNReal.ofReal (Real.exp (w x) / M)) :=
    (hw.exp.div_const M).ennreal_ofReal
  have htop : ∀ᵐ x ∂μ,
      ENNReal.ofReal (Real.exp (w x) / M) < ⊤ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  rw [normalizedTilt, integrable_withDensity_iff_integrable_smul' hden htop]
  have he : (fun x =>
      (ENNReal.ofReal (Real.exp (w x) / M)).toReal • f x) =
      fun x => (Real.exp (w x) * f x) / M := by
    funext x
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.exp (w x) / M)]
    simp only [smul_eq_mul]
    ring
  rw [he]
  constructor
  · intro hi
    have hm := hi.mul_const M
    simpa only [div_mul_cancel₀ _ hM.ne'] using hm
  · intro hi
    exact hi.mul_const (M⁻¹) |>.congr (by
      filter_upwards [] with x
      ring)

end SlowEquilibration.ConditionedEntrance
