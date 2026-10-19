-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceReductionClosedBandGraph
public import SlowEquilibration.SphericalKacRiceHittingSource

@[expose] public section

/-! Closed critical-center path-hit graph for the literal original tensor
field and continuous sphere paths. This is the compact-projection component
of manuscript Lemma `red-unions` (b). -/

namespace SlowEquilibration.SourceReductionClosedPathUnionGraph
noncomputable section
open Set MeasureTheory ProbabilityTheory SphericalModel SphericalKacRiceHittingSource
open SourceReductionClosedBandGraph
open SphericalRealTimePathKernel SphericalRotationCovariance
open SphericalAging.HardSphereDynamics PairConditionalDeterminantMoments
open SphericalFieldKernels
open scoped Topology RealInnerProductSpace NNReal
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.style.haveILetI false

variable {N : ℕ}

/-- There is a window critical center whose physical cap is visited by the
continuous path before the terminal time. -/
def closedPathHitUnionGraph (μ : FiniteMixture) (Q m M a : ℝ)
    (U : Set ℝ) (T : ℝ≥0) :
    Set (Disorder N μ.maxDegree × RealSpherePath N T) :=
  SourceReductionCompactBandProjection.bandUnionGraph
    {z : Disorder N μ.maxDegree × PhysicalSphere N |
      (z.1,z.2.1) ∈ windowCenterGraph μ Q m M U}
    (overlapSupEvent T a)

theorem closedPathHitUnionGraph_isClosed (μ : FiniteMixture)
    (Q m M a : ℝ) {U : Set ℝ} (hU : IsClosed U) (T : ℝ≥0) :
    IsClosed (closedPathHitUnionGraph (N := N) μ Q m M a U T) := by
  have hS : IsCompact {x : Vector N | OnSphere x} := by
    convert sourceSphere_compact N using 1
    ext x
    exact onSphere_iff_norm_sq x
  letI : CompactSpace (PhysicalSphere N) :=
    isCompact_iff_compactSpace.mp hS
  have hC : IsClosed
      {z : Disorder N μ.maxDegree × PhysicalSphere N |
        (z.1,z.2.1) ∈ windowCenterGraph μ Q m M U} :=
    (windowCenterGraph_isClosed μ Q m M hU).preimage
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hB : IsClosed (overlapSupEvent (N := N) T a) :=
    isClosed_le continuous_const (realPathMaximumOverlap_continuous T)
  exact SourceReductionCompactBandProjection.bandUnionGraph_isClosed hC hB

/-- The exact original tensor-field diffusion, started from the physical
uniform sphere, visits at least one selected critical center's cap. -/
def actualWindowPathHitProbability (hN : 2 ≤ N) (μ : FiniteMixture)
    (Q m M a β : ℝ) (U : Set ℝ) (T : ℝ≥0)
    (J : Disorder N μ.maxDegree) : ℝ :=
  let κ : Kernel (Disorder N μ.maxDegree) (RealSpherePath N T) :=
    (uniformRealPathKernel hN μ β T).comap (fieldMap μ)
      (fieldMap (N := N) μ).measurable
  (κ J).real {p | (J,p) ∈ closedPathHitUnionGraph μ Q m M a U T}

theorem actualWindowPathHitProbability_measurable (hN : 2 ≤ N)
    (μ : FiniteMixture) (Q m M a β : ℝ)
    {U : Set ℝ} (hU : IsClosed U) (T : ℝ≥0) :
    Measurable (actualWindowPathHitProbability hN μ Q m M a β U T) := by
  let κ : Kernel (Disorder N μ.maxDegree) (RealSpherePath N T) :=
    (uniformRealPathKernel hN μ β T).comap (fieldMap μ)
      (fieldMap (N := N) μ).measurable
  have hE : MeasurableSet (closedPathHitUnionGraph μ Q m M a U T) :=
    (closedPathHitUnionGraph_isClosed (N := N) μ Q m M a hU T).measurableSet
  change Measurable (fun J => (κ J).real
    (Prod.mk J ⁻¹' closedPathHitUnionGraph μ Q m M a U T))
  exact (Kernel.measurable_kernel_prodMk_left (κ := κ) hE).ennreal_toReal

end
end SlowEquilibration.SourceReductionClosedPathUnionGraph
