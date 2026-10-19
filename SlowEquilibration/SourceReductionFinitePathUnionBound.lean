-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourceReductionClosedPathUnionGraph
public import SlowEquilibration.SourceReductionFiniteCentersAE

/-! The finite-center union bound for the literal original-disorder
spherical diffusion path event in manuscript Lemma `red-unions` (c). -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceReductionFinitePathUnionBound
open Set MeasureTheory ProbabilityTheory SphericalModel
open SourceReductionClosedBandGraph SourceReductionClosedPathUnionGraph
open SphericalKacRiceHittingSource SphericalRealTimePathKernel
open SphericalRotationCovariance SphericalFieldKernels
open scoped NNReal ENNReal RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option linter.style.haveILetI false

variable {N : ℕ}

/-- For fixed disorder, the centers viewed as points of the physical sphere. -/
def physicalWindowCenters (μ : FiniteMixture) (Q m M : ℝ)
    (U : Set ℝ) (J : Disorder N μ.maxDegree) : Set (PhysicalSphere N) :=
  {u | (J,u.1) ∈ windowCenterGraph μ Q m M U}

theorem physicalWindowCenters_finite (μ : FiniteMixture) (Q m M : ℝ)
    (U : Set ℝ) (J : Disorder N μ.maxDegree)
    (hfinite : (windowCenters μ Q m M U J).Finite) :
    (physicalWindowCenters μ Q m M U J).Finite := by
  change ((Subtype.val : PhysicalSphere N → Vector N) ⁻¹'
    windowCenters μ Q m M U J).Finite
  exact hfinite.preimage (fun a _ b _ hab => Subtype.ext hab)

/-- The closed path-hit union is exactly the finite union of the individual
center cap-hit events on each fixed disorder fiber. -/
theorem closedPathHitUnionGraph_fiber_eq_iUnion (μ : FiniteMixture)
    (Q m M a : ℝ) (U : Set ℝ) (T : ℝ≥0)
    (J : Disorder N μ.maxDegree) :
    {p | (J,p) ∈ closedPathHitUnionGraph μ Q m M a U T} =
      ⋃ u : physicalWindowCenters μ Q m M U J,
        {p | (p,u.1) ∈ overlapSupEvent T a} := by
  ext p
  change (∃ u : PhysicalSphere N,
      (J,u.1) ∈ windowCenterGraph μ Q m M U ∧
      (p,u) ∈ overlapSupEvent T a) ↔ _
  constructor
  · rintro ⟨u,hu,hp⟩
    exact Set.mem_iUnion.mpr ⟨⟨u,hu⟩,hp⟩
  · intro hp
    obtain ⟨u,hu⟩ := Set.mem_iUnion.mp hp
    exact ⟨u.1,u.2,hu⟩

/-- The actual Brownian path probability of hitting any selected critical
center is at most the sum of its literal one-center path probabilities. -/
theorem actualWindowPathHitProbability_le_sum (hN : 2 ≤ N)
    (μ : FiniteMixture) (Q m M a β : ℝ) (U : Set ℝ)
    (T : ℝ≥0) (J : Disorder N μ.maxDegree)
    (hfinite : (windowCenters μ Q m M U J).Finite) :
    actualWindowPathHitProbability hN μ Q m M a β U T J ≤
      ∑ u ∈ (physicalWindowCenters_finite μ Q m M U J hfinite).toFinset,
        ((uniformRealPathKernel hN μ β T (fieldMap μ J)).real
          {p | (p,u) ∈ overlapSupEvent T a}) := by
  let s := physicalWindowCenters μ Q m M U J
  have hs : s.Finite := physicalWindowCenters_finite μ Q m M U J hfinite
  let κ : Kernel (Disorder N μ.maxDegree) (RealSpherePath N T) :=
    (uniformRealPathKernel hN μ β T).comap (fieldMap μ)
      (fieldMap (N := N) μ).measurable
  have hκ : κ J = uniformRealPathKernel hN μ β T (fieldMap μ J) := by
    rfl
  change (κ J).real {p | (J,p) ∈ closedPathHitUnionGraph μ Q m M a U T} ≤ _
  rw [closedPathHitUnionGraph_fiber_eq_iUnion]
  rw [show (⋃ u : s, {p | (p,u.1) ∈ overlapSupEvent T a}) =
      ⋃ u ∈ hs.toFinset, {p | (p,u) ∈ overlapSupEvent T a} by
    ext p
    simp only [Set.mem_iUnion, hs.mem_toFinset]
    constructor
    · rintro ⟨u,hu⟩
      exact ⟨u.1,u.2,hu⟩
    · rintro ⟨u,hu,hp⟩
      exact ⟨⟨u,hu⟩,hp⟩]
  simpa only [hκ] using
    (measureReal_biUnion_finset_le (μ := κ J) hs.toFinset
      (fun u : PhysicalSphere N => {p | (p,u) ∈ overlapSupEvent T a}))

end SlowEquilibration.SourceReductionFinitePathUnionBound
