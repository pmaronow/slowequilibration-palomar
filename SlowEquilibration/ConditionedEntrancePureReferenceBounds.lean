-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ConditionedEntrancePureBaseField

/-! Original-reference bounds under the actual Gibbs law of an arbitrary
smooth field, including the proper-pure source cutoff. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
open MeasureTheory SphericalModel SphericalForm
open SphericalAging HardSphereDynamics
open scoped NNReal
set_option autoImplicit false
set_option maxHeartbeats 300000

theorem referenceInitial_field_bounds {N : ℕ} (D D₀ : FieldData N)
    (β : ℝ) (hβ : 0 ≤ β) (B : ℝ)
    (hB : ∀ x, OnSphere x → |D₀.hamiltonian x| ≤ B) :
    ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,
      1 ≤ 1+uniformInitialDensity N β D₀.hamiltonian x ∧
      1+uniformInitialDensity N β D₀.hamiltonian x ≤ 1+Real.exp (2*β*B) := by
  filter_upwards [gibbsLaw_support D.dimension_ge_one β D.hamiltonian] with x hx
  have hb := uniformInitialDensity_le D.dimension_ge_one β hβ D₀.hamiltonian
    D₀.hamiltonian_contDiff.continuous B hB x ((onSphere_iff_norm_sq x).mpr hx)
  have hp := uniformInitialDensity_pos D.dimension_ge_one β D₀.hamiltonian
    D₀.hamiltonian_contDiff.continuous x
  constructor <;> linarith

theorem referenceRate_field_bounds {N : ℕ} (D D₀ : FieldData N)
    (β : ℝ) (hβ : 0 ≤ β) (θ : ℝ≥0) (hθ : 0 < θ) (B : ℝ)
    (hB : ∀ x, OnSphere x → |D₀.hamiltonian x| ≤ B) :
    ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,
      1 ≤ referenceRate D₀ β θ (referenceInitialVector D₀ β) x ∧
      referenceRate D₀ β θ (referenceInitialVector D₀ β) x ≤
        1+Real.exp (2*β*B) := by
  have hb := referenceRate_bounds D₀ β θ hθ (referenceInitialVector D₀ β)
    1 (1+Real.exp (2*β*B)) (referenceInitialVector_bounds D₀ β hβ B hB)
  exact hb.filter_mono (gibbsLaw_absolutelyContinuous_gibbsLaw
    D.dimension_ge_one β β D₀.hamiltonian D.hamiltonian
    D₀.hamiltonian_contDiff.continuous).ae_le

end SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
