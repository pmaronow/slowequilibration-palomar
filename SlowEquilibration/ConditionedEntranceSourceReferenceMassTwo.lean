-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceReferenceBounds

/-! The literal unperturbed source reference resolvent has mass two.
Its positive representative may be used in pointwise hazard inequalities
without altering any Gibbs pairing. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance.SmoothKilled
open SphericalModel SphericalForm
set_option autoImplicit false
set_option maxHeartbeats 300000
variable {N : ℕ}

def sourceReferencePositivePart (D : SourceData N) (β : ℝ) (θ : ℝ≥0)
    (x : Vector N) : ℝ :=
  max 0 (referenceRate D.baseData β θ (referenceInitialVector D.baseData β) x)

/-- Clipping the actual base reference resolvent at zero changes it only
on a Gibbs-null set. -/
theorem sourceReferencePositivePart_ae (D : SourceData N) (β : ℝ)
    (θ : ℝ≥0) :
    (fun x => sourceReferencePositivePart D β θ x) =ᵐ[
      gibbsLaw N β D.baseData.hamiltonian]
      referenceRate D.baseData β θ (referenceInitialVector D.baseData β) := by
  have hU : ∀ᵐ x ∂gibbsLaw N β D.baseData.hamiltonian,
      0 ≤ referenceInitialVector D.baseData β x := by
    filter_upwards [referenceInitialVector_ae D.baseData β] with x hx
    rw [hx]
    have hp := uniformInitialDensity_pos D.dimension_ge_one β
      D.baseData.hamiltonian D.baseData.hamiltonian_contDiff.continuous x
    linarith
  have hF := referenceRate_nonnegative D.baseData β θ
    (referenceInitialVector D.baseData β) hU
  exact hF.mono (fun x hx => by
    change max 0 (referenceRate D.baseData β θ
      (referenceInitialVector D.baseData β) x) = _
    exact max_eq_right hx)

theorem sourceReferencePositivePart_integrable (D : SourceData N) (β : ℝ)
    (θ : ℝ≥0) :
    Integrable (sourceReferencePositivePart D β θ)
      (gibbsLaw N β D.baseData.hamiltonian) := by
  let : IsProbabilityMeasure (gibbsLaw N β D.baseData.hamiltonian) :=
    gibbsLaw_probability D.dimension_ge_one β D.baseData.hamiltonian_contDiff.continuous
  have hi : Integrable
      (fun x => referenceRate D.baseData β θ
        (referenceInitialVector D.baseData β) x)
      (gibbsLaw N β D.baseData.hamiltonian) :=
    (Lp.memLp (referenceRate D.baseData β θ
      (referenceInitialVector D.baseData β))).integrable (by norm_num)
  exact hi.congr (sourceReferencePositivePart_ae D β θ).symm

/-- The exact two units of mass are the constant reference plus the
uniform-start inverse Gibbs density, preserved by the base resolvent. -/
theorem sourceReferencePositivePart_mass_two (D : SourceData N) (β : ℝ)
    (θ : ℝ≥0) (hθ : 0 < θ) :
    (∫ x, sourceReferencePositivePart D β θ x
      ∂gibbsLaw N β D.baseData.hamiltonian) = 2 := by
  rw [integral_congr_ae (sourceReferencePositivePart_ae D β θ)]
  rw [referenceRate_mass D.baseData β θ hθ]
  exact referenceInitialVector_mass D.baseData β

end SlowEquilibration.ConditionedEntrance.SmoothKilled
