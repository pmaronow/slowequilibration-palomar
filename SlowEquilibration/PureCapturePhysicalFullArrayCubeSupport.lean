-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalAsymptoticFullLift

/-! Closed bounded-overlap support survives physical weak limits.
This explicit support theorem is useful when transferring polynomial
covariance moments through weak convergence. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalFullArrayCubeSupport

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalAsymptoticFullLift
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def cubeFullOverlapLawArrays : Set FullOverlapLawArray :=
  {x | ∀ m, ∀ᵐ c ∂(x m : Measure (FullOverlapCoordinates m)),
    c ∈ fullOverlapCube m}

theorem cubeFullOverlapLawArrays_closed :
    IsClosed cubeFullOverlapLawArrays := by
  unfold cubeFullOverlapLawArrays
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro m
  have hcont : Continuous (fun x : FullOverlapLawArray => x m) := continuous_apply m
  exact IsClosed.preimage hcont
    (supportedProbabilityLaws_closed (fullOverlapCube_compact m).isClosed)

theorem physicalFullOverlapArrayLimitSet_cube
    (μ : FiniteMixture) (β : ℝ)
    {x : FullOverlapLawArray}
    (hx : x ∈ physicalFullOverlapArrayLimitSet μ β) :
    x ∈ cubeFullOverlapLawArrays := by
  apply closure_minimal _ cubeFullOverlapLawArrays_closed hx
  rintro x ⟨n, rfl⟩ m
  exact physicalFullOverlapLaw_cube_ae μ β

theorem physicalFullAsymptoticLimitSet_cube
    (μ : FiniteMixture) (β : ℝ)
    {x : FullOverlapLawArray}
    (hx : x ∈ physicalFullAsymptoticLimitSet μ β) :
    x ∈ cubeFullOverlapLawArrays :=
  physicalFullOverlapArrayLimitSet_cube μ β
    (physicalFullAsymptoticLimitSet_subset μ β hx)

end SlowEquilibration.PureCapturePhysicalFullArrayCubeSupport
