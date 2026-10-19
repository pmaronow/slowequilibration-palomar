-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalWindowGeometry
public import SlowEquilibration.SourcePhysicalPairSelectionRegularity
public import SlowEquilibration.SourceReductionCompactBandProjection

/-! Closed center and band graphs for the original spherical tensor field,
corresponding to the topological part of manuscript Lemma `red-unions`. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceReductionClosedBandGraph

open Set SphericalModel SphericalGaussianJet SphericalMarkedWindows
open PairConditionalDeterminantMoments SphericalForm
open scoped Topology RealInnerProductSpace

variable {N : ℕ}
set_option maxHeartbeats 600000

/-- Literal physical sphere, center gradient, energy window and normalized
radial-mark window, viewed as a closed graph in ambient tensor coordinates. -/
def windowCenterGraph (μ : FiniteMixture) (Q m M : ℝ) (U : Set ℝ) :
    Set (Disorder N μ.maxDegree × Vector N) :=
  let c := centerCoefficients (mixtureCoefficients μ) Q
  {z | ‖z.2‖ ^ 2 = (N : ℝ)} ∩
  {z | surfaceGradient (field c z.1) z.2 = 0} ∩
  {z | field c z.1 z.2 ∈ Icc (m-M) (m+M)} ∩
  {z | (actualScore c z.1 z.2) 1 ∈ U}

attribute [local irreducible] windowCenterGraph

theorem windowCenterGraph_isClosed (μ : FiniteMixture) (Q m M : ℝ)
    {U : Set ℝ} (hU : IsClosed U) :
    IsClosed (windowCenterGraph (N := N) μ Q m M U) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hs : IsClosed {z : Disorder N μ.maxDegree × Vector N |
      ‖z.2‖ ^ 2 = (N : ℝ)} :=
    isClosed_eq (continuous_snd.norm.pow 2) continuous_const
  have hg : IsClosed {z : Disorder N μ.maxDegree × Vector N |
      surfaceGradient (field c z.1) z.2 = 0} :=
    isClosed_eq (source_surfaceGradient_joint_contDiff c).continuous continuous_const
  have hv : IsClosed {z : Disorder N μ.maxDegree × Vector N |
      field c z.1 z.2 ∈ Icc (m-M) (m+M)} :=
    isClosed_Icc.preimage (field_jointContinuous c)
  have hr : IsClosed {z : Disorder N μ.maxDegree × Vector N |
      (actualScore c z.1 z.2) 1 ∈ U} :=
    hU.preimage ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp
      (actualScore_jointContinuous c))
  unfold windowCenterGraph
  exact ((hs.inter hg).inter hv).inter hr

/-- The corresponding source window centers at a fixed actual disorder. -/
def windowCenters (μ : FiniteMixture) (Q m M : ℝ) (U : Set ℝ)
    (J : Disorder N μ.maxDegree) : Set (Vector N) :=
  {u | (J,u) ∈ windowCenterGraph μ Q m M U}

/-- The source band relation, with the original normalized overlap. -/
def physicalBandRelation (Q b : ℝ) : Set (Vector N × Vector N) :=
  {z | |overlap z.1 z.2 - Real.sqrt Q| ≤ b}

theorem physicalBandRelation_isClosed (Q b : ℝ) :
    IsClosed (physicalBandRelation (N := N) Q b) := by
  unfold physicalBandRelation
  have hR : Continuous (fun z : Vector N × Vector N => overlap z.1 z.2) := by
    unfold overlap
    exact (continuous_fst.inner continuous_snd).div_const _
  exact isClosed_Iic.preimage ((hR.sub continuous_const).abs)

/-- The closed graph of the original critical-center band union. -/
def bandUnionGraph (μ : FiniteMixture) (Q m M b : ℝ) (U : Set ℝ) :
    Set (Disorder N μ.maxDegree × Vector N) :=
  SourceReductionCompactBandProjection.bandUnionGraph
    (windowCenterGraph μ Q m M U) (physicalBandRelation Q b)

theorem bandUnionGraph_isClosed (μ : FiniteMixture) (Q m M b : ℝ)
    {U : Set ℝ} (hU : IsClosed U) :
    IsClosed (bandUnionGraph (N := N) μ Q m M b U) := by
  let S : Set (Vector N) := {u | ‖u‖ ^ 2 = (N : ℝ)}
  let : CompactSpace S := isCompact_iff_compactSpace.mp (sourceSphere_compact N)
  let C : Set (Disorder N μ.maxDegree × S) :=
    {z | (z.1,z.2.1) ∈ windowCenterGraph μ Q m M U}
  let B : Set (Vector N × S) :=
    {z | (z.1,z.2.1) ∈ physicalBandRelation Q b}
  have hC : IsClosed C :=
    (windowCenterGraph_isClosed μ Q m M hU).preimage
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hB : IsClosed B :=
    (physicalBandRelation_isClosed Q b).preimage
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hProj := SourceReductionCompactBandProjection.bandUnionGraph_isClosed hC hB
  convert hProj using 1
  ext z
  constructor
  · rintro ⟨u, hu, hb⟩
    have hs : u ∈ S := by
      have h := hu
      unfold windowCenterGraph at h
      exact h.1.1.1
    exact ⟨⟨u,hs⟩,hu,hb⟩
  · rintro ⟨u,hu,hb⟩
    exact ⟨u.1,hu,hb⟩

/-- Restricting the point as well as the critical center to the original
radius-`√N` sphere gives the manuscript's closed band-union graph. -/
def physicalSphereBandUnionGraph (μ : FiniteMixture) (Q m M b : ℝ)
    (U : Set ℝ) : Set (Disorder N μ.maxDegree × Vector N) :=
  bandUnionGraph μ Q m M b U ∩ {z | ‖z.2‖ ^ 2 = (N : ℝ)}

theorem physicalSphereBandUnionGraph_isClosed (μ : FiniteMixture)
    (Q m M b : ℝ) {U : Set ℝ} (hU : IsClosed U) :
    IsClosed (physicalSphereBandUnionGraph (N := N) μ Q m M b U) := by
  unfold physicalSphereBandUnionGraph
  exact (bandUnionGraph_isClosed μ Q m M b hU).inter
    (isClosed_eq (continuous_snd.norm.pow 2) continuous_const)

end SlowEquilibration.SourceReductionClosedBandGraph
