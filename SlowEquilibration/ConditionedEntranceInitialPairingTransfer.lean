-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceActualSourceInitialL1

/-! Transfer of a bounded killed-resolvent test from the literal uniform
initial density to the base reference density under the global source tilt. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false

/-- An actual unit-interval killed-resolvent representative incurs at most
the total-variation error when the physical initial density is replaced by
the original Gibbs reference density. -/
theorem initialDensity_pairing_le_reference_add_l1
    {E : Type*} [MeasurableSpace E] (ν : Measure E)
    (q₀ f₀ h : E → ℝ)
    (hq : Integrable q₀ ν) (hf : Integrable f₀ ν)
    (hh : AEStronglyMeasurable h ν)
    (hhb : ∀ᵐ z ∂ν, 0 ≤ h z ∧ h z ≤ 1) :
    (∫ z, q₀ z * h z ∂ν) ≤
      (∫ z, f₀ z * h z ∂ν) + ∫ z, |q₀ z - f₀ z| ∂ν := by
  have hnorm : ∀ᵐ z ∂ν, ‖h z‖ ≤ 1 := hhb.mono (fun z hz => by
    rw [Real.norm_eq_abs, abs_of_nonneg hz.1]
    exact hz.2)
  have hqi : Integrable (fun z => q₀ z * h z) ν :=
    hq.mul_bdd hh hnorm
  have hfi : Integrable (fun z => f₀ z * h z) ν :=
    hf.mul_bdd hh hnorm
  have hdi : Integrable (fun z => |q₀ z - f₀ z|) ν := (hq.sub hf).abs
  have hpoint : ∀ᵐ z ∂ν,
      q₀ z * h z ≤ f₀ z * h z + |q₀ z - f₀ z| := by
    filter_upwards [hhb] with z hz
    have hbound : (q₀ z - f₀ z) * h z ≤ |q₀ z - f₀ z| := by
      by_cases hd : 0 ≤ q₀ z - f₀ z
      · rw [abs_of_nonneg hd]
        exact mul_le_of_le_one_right hd hz.2
      · have hneg : q₀ z - f₀ z ≤ 0 := le_of_not_ge hd
        have hp := mul_nonpos_of_nonpos_of_nonneg hneg hz.1
        exact hp.trans (abs_nonneg _)
    linarith
  have hi := integral_mono_ae hqi (hfi.add hdi) hpoint
  simpa only [Pi.add_apply, integral_add hfi hdi] using hi

end SlowEquilibration.ConditionedEntrance
