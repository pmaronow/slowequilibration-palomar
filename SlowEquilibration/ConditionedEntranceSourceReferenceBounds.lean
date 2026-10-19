-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceBaseJointFisher
public import SlowEquilibration.SphericalGibbsEquivalentMeasures

/-! True original-bank bounds for the entropy initial density and
physical reference, evaluated under the source Gibbs law. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.SmoothKilled
open SphericalModel SphericalForm SphericalAging.HardSphereDynamics
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

theorem regular_base_field_bound (D : SourceData N) (hJ : D.disorder∈regularDisorder)
    (x : Vector N) (hx : OnSphere x) :
    |D.baseData.hamiltonian x|≤derivativeConstant (mixtureCoefficients D.mixture)*(N : ℝ) := by
  rw [SourceData.baseData_hamiltonian]
  have hn := SphericalAging.LandscapeDerivatives.sphere_norm x ((onSphere_iff_norm_sq x).mp hx)
  exact (field_regularDisorder_ball_bounds D.dimension_ge_one (mixtureCoefficients D.mixture)
    D.disorder hJ x (by rw [hn])).1

theorem referenceInitial_source_regular_bounds (D : SourceData N) (β : ℝ) (hβ : 0≤β)
    (hJ : D.disorder∈regularDisorder) :
    ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,
      1≤1+uniformInitialDensity N β D.baseData.hamiltonian x ∧
      1+uniformInitialDensity N β D.baseData.hamiltonian x≤
        1+Real.exp (2*β*derivativeConstant (mixtureCoefficients D.mixture)*(N : ℝ)) := by
  filter_upwards [gibbsLaw_support D.dimension_ge_one β D.hamiltonian] with x hx
  have hb := uniformInitialDensity_le D.dimension_ge_one β hβ D.baseData.hamiltonian
    D.baseData.hamiltonian_contDiff.continuous
    (derivativeConstant (mixtureCoefficients D.mixture)*(N : ℝ)) (regular_base_field_bound D hJ)
    x ((onSphere_iff_norm_sq x).mpr hx)
  have hp := uniformInitialDensity_pos D.dimension_ge_one β D.baseData.hamiltonian
    D.baseData.hamiltonian_contDiff.continuous x
  constructor
  · linarith
  · simpa only [mul_assoc,add_comm] using add_le_add_left hb 1

theorem referenceRate_source_regular_bounds (D : SourceData N) (β : ℝ) (hβ : 0≤β)
    (θ : ℝ≥0) (hθ : 0<θ) (hJ : D.disorder∈regularDisorder) :
    ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,
      1≤referenceRate D.baseData β θ (referenceInitialVector D.baseData β) x ∧
      referenceRate D.baseData β θ (referenceInitialVector D.baseData β) x≤
        1+Real.exp (2*β*derivativeConstant (mixtureCoefficients D.mixture)*(N : ℝ)) := by
  have hb := referenceRate_bounds D.baseData β θ hθ (referenceInitialVector D.baseData β) 1
    (1+Real.exp (2*β*(derivativeConstant (mixtureCoefficients D.mixture)*(N : ℝ))))
    (referenceInitialVector_bounds D.baseData β hβ
      (derivativeConstant (mixtureCoefficients D.mixture)*(N : ℝ)) (regular_base_field_bound D hJ))
  have hAC := (gibbsLaw_absolutelyContinuous_gibbsLaw D.dimension_ge_one β β D.baseData.hamiltonian
    D.hamiltonian D.baseData.hamiltonian_contDiff.continuous).ae_le
  simpa only [mul_assoc] using hb.filter_mono hAC

end SlowEquilibration.ConditionedEntrance.SmoothKilled
