-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceReductionFinitePathUnionBound

/-! Every one-time visit to the union of actual critical-center caps is a
visit of the corresponding continuous-path hit event. -/

@[expose] public section
namespace SlowEquilibration.SourceReductionPointCapMass
noncomputable section
open Set MeasureTheory ProbabilityTheory SphericalModel
open SourceReductionClosedBandGraph SourceReductionClosedPathUnionGraph
open SourceReductionFinitePathUnionBound SourceReductionCompactBandProjection
open SphericalKacRiceHittingSource SphericalRealTimePathKernel
open SphericalRotationCovariance SphericalFieldKernels
open SphericalAging.HardSphereDynamics PairConditionalDeterminantMoments
open scoped NNReal ENNReal RealInnerProductSpace Topology
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

variable {N : ℕ}

def pointCapRelation (a : ℝ) : Set (PhysicalSphere N × PhysicalSphere N) :=
  {z | a ≤ |overlap z.1.1 z.2.1|}

theorem pointCapRelation_isClosed (a : ℝ) :
    IsClosed (pointCapRelation (N := N) a) := by
  have hR : Continuous (fun z : PhysicalSphere N × PhysicalSphere N =>
      overlap z.1.1 z.2.1) := by
    unfold overlap
    exact (((continuous_subtype_val.comp continuous_fst).inner
      (continuous_subtype_val.comp continuous_snd)).div_const _)
  exact isClosed_le continuous_const hR.abs

def pointCapUnionGraph (μ : FiniteMixture) (Q m M a : ℝ)
    (U : Set ℝ) : Set (Disorder N μ.maxDegree × PhysicalSphere N) :=
  SourceReductionCompactBandProjection.bandUnionGraph
    {z : Disorder N μ.maxDegree × PhysicalSphere N |
      (z.1,z.2.1) ∈ windowCenterGraph μ Q m M U}
    (pointCapRelation a)

theorem pointCapUnionGraph_isClosed (μ : FiniteMixture)
    (Q m M a : ℝ) {U : Set ℝ} (hU : IsClosed U) :
    IsClosed (pointCapUnionGraph (N := N) μ Q m M a U) := by
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
  exact SourceReductionCompactBandProjection.bandUnionGraph_isClosed hC
    (pointCapRelation_isClosed a)

theorem pointCapUnionGraph_fiber_iff (μ : FiniteMixture)
    (Q m M a : ℝ) (U : Set ℝ) (J : Disorder N μ.maxDegree)
    (x : PhysicalSphere N) :
    (J,x) ∈ pointCapUnionGraph μ Q m M a U ↔
      ∃ u : PhysicalSphere N,
        (J,u.1) ∈ windowCenterGraph μ Q m M U ∧
          a ≤ |overlap x.1 u.1| := Iff.rfl

/-- The one-time physical path marginal has no more mass in the selected
cap union than the actual continuous path-hit union. -/
theorem uniformRealPathKernel_pointCap_le_hit (hN : 2 ≤ N)
    (μ : FiniteMixture) (Q m M a β : ℝ)
    {U : Set ℝ} (hU : IsClosed U) (T : ℝ≥0)
    (J : Disorder N μ.maxDegree) (t : RealPathTime T) :
    (uniformRealPathKernel hN μ β T (fieldMap μ J)).real
      {p | (J,p t) ∈ pointCapUnionGraph μ Q m M a U} ≤
      actualWindowPathHitProbability hN μ Q m M a β U T J := by
  let κ := uniformRealPathKernel hN μ β T (fieldMap μ J)
  have hE : MeasurableSet
      {p : RealSpherePath N T |
        (J,p t) ∈ pointCapUnionGraph μ Q m M a U} :=
    (pointCapUnionGraph_isClosed (N := N) μ Q m M a hU).measurableSet.preimage
      (measurable_const.prodMk (ContinuousMap.measurable_eval t))
  have hF : MeasurableSet
      {p : RealSpherePath N T |
        (J,p) ∈ closedPathHitUnionGraph μ Q m M a U T} :=
    (closedPathHitUnionGraph_isClosed (N := N) μ Q m M a hU T).measurableSet.preimage
      (measurable_const.prodMk measurable_id)
  have hsubset :
      {p : RealSpherePath N T |
        (J,p t) ∈ pointCapUnionGraph μ Q m M a U} ⊆
      {p | (J,p) ∈ closedPathHitUnionGraph μ Q m M a U T} := by
    intro p hp
    obtain ⟨u,hu,ha⟩ := (pointCapUnionGraph_fiber_iff μ Q m M a U J (p t)).mp hp
    change ∃ u : PhysicalSphere N,
      (J,u.1) ∈ windowCenterGraph μ Q m M U ∧
      (p,u) ∈ overlapSupEvent T a
    exact ⟨u,hu,(realPathMaximumOverlap_ge_iff T a (p,u)).mpr ⟨t,ha⟩⟩
  change κ.real _ ≤ κ.real _
  exact measureReal_mono hsubset

end
end SlowEquilibration.SourceReductionPointCapMass
