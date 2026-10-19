-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureReferenceBounds

/-! The literal unperturbed source reference resolvent has mass two.
Its positive representative may be used in pointwise hazard inequalities
without altering any Gibbs pairing. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
open SphericalModel SphericalForm
set_option autoImplicit false
set_option maxHeartbeats 300000
variable {N : ℕ}

def fieldReferencePositivePart (D : FieldData N) (β : ℝ) (θ : ℝ≥0)
    (x : Vector N) : ℝ :=
  max 0 (referenceRate D β θ (referenceInitialVector D β) x)

/-- Clipping the actual base reference resolvent at zero changes it only
on a Gibbs-null set. -/
theorem fieldReferencePositivePart_ae (D : FieldData N) (β : ℝ)
    (θ : ℝ≥0) :
    (fun x => fieldReferencePositivePart D β θ x) =ᵐ[
      gibbsLaw N β D.hamiltonian]
      referenceRate D β θ (referenceInitialVector D β) := by
  have hU : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,
      0 ≤ referenceInitialVector D β x := by
    filter_upwards [referenceInitialVector_ae D β] with x hx
    rw [hx]
    have hp := uniformInitialDensity_pos D.dimension_ge_one β
      D.hamiltonian D.hamiltonian_contDiff.continuous x
    linarith
  have hF := referenceRate_nonnegative D β θ
    (referenceInitialVector D β) hU
  exact hF.mono (fun x hx => by
    change max 0 (referenceRate D β θ
      (referenceInitialVector D β) x) = _
    exact max_eq_right hx)

theorem fieldReferencePositivePart_integrable (D : FieldData N) (β : ℝ)
    (θ : ℝ≥0) :
    Integrable (fieldReferencePositivePart D β θ)
      (gibbsLaw N β D.hamiltonian) := by
  let : IsProbabilityMeasure (gibbsLaw N β D.hamiltonian) :=
    gibbsLaw_probability D.dimension_ge_one β D.hamiltonian_contDiff.continuous
  have hi : Integrable
      (fun x => referenceRate D β θ
        (referenceInitialVector D β) x)
      (gibbsLaw N β D.hamiltonian) :=
    (Lp.memLp (referenceRate D β θ
      (referenceInitialVector D β))).integrable (by norm_num)
  exact hi.congr (fieldReferencePositivePart_ae D β θ).symm

/-- The exact two units of mass are the constant reference plus the
uniform-start inverse Gibbs density, preserved by the base resolvent. -/
theorem fieldReferencePositivePart_mass_two (D : FieldData N) (β : ℝ)
    (θ : ℝ≥0) (hθ : 0 < θ) :
    (∫ x, fieldReferencePositivePart D β θ x
      ∂gibbsLaw N β D.hamiltonian) = 2 := by
  rw [integral_congr_ae (fieldReferencePositivePart_ae D β θ)]
  rw [referenceRate_mass D β θ hθ]
  exact referenceInitialVector_mass D β

end SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
