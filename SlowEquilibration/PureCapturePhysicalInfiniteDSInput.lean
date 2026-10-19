-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalInfiniteAsymptoticLift

/-! The countably infinite physical weak-limit laws satisfy the precise
finite-principal-matrix constraints used by Dovbysh--Sudakov: positive
semidefiniteness, unit diagonal, and weak exchangeability. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalInfiniteDSInput

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalInfiniteArrayTightness
open PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalInfiniteAsymptoticLift
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem physicalInfiniteAsymptoticLimit_gram
    (μ : FiniteMixture) (β : ℝ)
    {ρ : ProbabilityMeasure InfiniteOverlapCoordinates}
    (hρ : ρ ∈ physicalInfiniteAsymptoticLimitSet μ β) :
    ∀ᵐ c ∂(ρ : Measure InfiniteOverlapCoordinates),
      ∀ m, infiniteTruncate m c ∈ fullGramCone m := by
  rw [ae_all_iff]
  intro m
  have hfull := physicalFullOverlapArrayLimitSet_gram μ β
    (physicalFullAsymptoticLimitSet_subset μ β
      (infiniteToFullLawArray_maps_asymptotic_limits μ β hρ))
  have hm := hfull m
  change ∀ᵐ c ∂((ρ.map (infiniteTruncate m) :
    ProbabilityMeasure (FullOverlapCoordinates m)) :
      Measure (FullOverlapCoordinates m)), c ∈ fullGramCone m at hm
  exact (ae_map_iff (infiniteTruncate_continuous m).measurable.aemeasurable
    (fullGramCone_closed m).measurableSet).mp hm

theorem physicalInfiniteAsymptoticLimit_unitDiagonal
    (μ : FiniteMixture) (β : ℝ)
    {ρ : ProbabilityMeasure InfiniteOverlapCoordinates}
    (hρ : ρ ∈ physicalInfiniteAsymptoticLimitSet μ β) :
    ∀ᵐ c ∂(ρ : Measure InfiniteOverlapCoordinates),
      ∀ m, infiniteTruncate m c ∈ fullUnitDiagonal m := by
  rw [ae_all_iff]
  intro m
  have hfull := physicalFullOverlapArrayLimitSet_unitDiagonal μ β
    (physicalFullAsymptoticLimitSet_subset μ β
      (infiniteToFullLawArray_maps_asymptotic_limits μ β hρ))
  have hm := hfull m
  change ∀ᵐ c ∂((ρ.map (infiniteTruncate m) :
    ProbabilityMeasure (FullOverlapCoordinates m)) :
      Measure (FullOverlapCoordinates m)), c ∈ fullUnitDiagonal m at hm
  exact (ae_map_iff (infiniteTruncate_continuous m).measurable.aemeasurable
    (fullUnitDiagonal_closed m).measurableSet).mp hm

theorem physicalInfiniteAsymptoticLimit_exchangeable
    (μ : FiniteMixture) (β : ℝ)
    {ρ : ProbabilityMeasure InfiniteOverlapCoordinates}
    (hρ : ρ ∈ physicalInfiniteAsymptoticLimitSet μ β)
    (m : ℕ) (e : Equiv.Perm (Fin m)) :
    (ρ.map (infiniteTruncate m)).map (permuteFullOverlap e) =
      ρ.map (infiniteTruncate m) := by
  exact (physicalFullOverlapArrayLimitSet_exchangeable μ β
    (physicalFullAsymptoticLimitSet_subset μ β
      (infiniteToFullLawArray_maps_asymptotic_limits μ β hρ))) m e

end SlowEquilibration.PureCapturePhysicalInfiniteDSInput
