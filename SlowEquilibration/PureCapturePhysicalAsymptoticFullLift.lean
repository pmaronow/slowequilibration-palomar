-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalAsymptoticScoreLimits

/-! Full overlap-array cluster points along dimensions tending to infinity,
and their exact projection onto asymptotic physical capture-score laws. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalAsymptoticFullLift

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCaptureOverlapScoreCoordinates
open PureCapturePhysicalScoreTightness
open PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalFullToScore
open PureCapturePhysicalAsymptoticScoreLimits
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def physicalFullAsymptoticLimitSet (μ : FiniteMixture)
    (β : ℝ) : Set FullOverlapLawArray :=
  tailClusterSet (physicalFullOverlapLawArray μ β)

theorem physicalFullAsymptoticLimitSet_compact
    (μ : FiniteMixture) (β : ℝ) :
    IsCompact (physicalFullAsymptoticLimitSet μ β) :=
  tailClusterSet_compact _ (physicalFullOverlapArrayLimitSet_compact μ β)

theorem physicalFullAsymptoticLimitSet_subset
    (μ : FiniteMixture) (β : ℝ) :
    physicalFullAsymptoticLimitSet μ β ⊆
      physicalFullOverlapArrayLimitSet μ β :=
  tailClusterSet_subset_closure_range _

theorem physicalFullAsymptoticLimitSet_tendsto_subseq
    (μ : FiniteMixture) (β : ℝ)
    (s : ℕ → ℕ) (hs : StrictMono s) :
    ∃ limitArray ∈ physicalFullAsymptoticLimitSet μ β,
      ∃ t : ℕ → ℕ, StrictMono t ∧
        Tendsto (fun j : ℕ => physicalFullOverlapLawArray μ β (s (t j)))
          atTop (𝓝 limitArray) := by
  obtain ⟨x, _, t, ht, hlim⟩ :=
    physicalFullOverlapArrayLimitSet_tendsto_subseq μ β s
  refine ⟨x, ?_, t, ht, hlim⟩
  apply (mem_tailClusterSet_iff_mapClusterPt _ _).2
  apply MapClusterPt.of_comp ((hs.comp ht).tendsto_atTop)
  exact hlim.mapClusterPt

theorem fullToScoreArray_maps_asymptotic_limits (k : ℕ)
    (μ : FiniteMixture) (β : ℝ)
    {x : FullOverlapLawArray}
    (hx : x ∈ physicalFullAsymptoticLimitSet μ β) :
    fullToScoreArray k x ∈ physicalScoreAsymptoticLimitSet k μ β := by
  have hcluster : MapClusterPt x atTop
      (physicalFullOverlapLawArray μ β) :=
    (mem_tailClusterSet_iff_mapClusterPt _ _).1 hx
  obtain ⟨s, hs, hfull⟩ := hcluster.tendsto_subseq
  have hscore : Tendsto
      (fun j : ℕ => fullToScoreArray k (physicalFullOverlapLawArray μ β (s j)))
      atTop (𝓝 (fullToScoreArray k x)) :=
    ((fullToScoreArray_continuous k).tendsto x).comp hfull
  apply (mem_tailClusterSet_iff_mapClusterPt _ _).2
  have hscoreMap : MapClusterPt (fullToScoreArray k x) atTop
      ((fun n => fullToScoreArray k (physicalFullOverlapLawArray μ β n)) ∘ s) := by
    simpa only [Function.comp_def] using hscore.mapClusterPt
  have hcluster' := MapClusterPt.of_comp hs.tendsto_atTop hscoreMap
  simpa only [fullToScoreArray_physical] using hcluster'

/-- Every asymptotic capture-score weak limit is the exact projection of
a full physical overlap-array weak limit along dimensions tending to
infinity. Thus a Dovbysh--Sudakov input need only cover genuine physical
asymptotic laws. -/
theorem physicalAsymptoticScoreLimit_exists_fullAsymptoticLimit (k : ℕ)
    (μ : FiniteMixture) (β : ℝ)
    {y : ScoreLawArray k}
    (hy : y ∈ physicalScoreAsymptoticLimitSet k μ β) :
    ∃ x ∈ physicalFullAsymptoticLimitSet μ β,
      fullToScoreArray k x = y := by
  obtain ⟨s, hs, hscore⟩ :=
    ((mem_tailClusterSet_iff_mapClusterPt _ _).1 hy).tendsto_subseq
  obtain ⟨x, hx, t, ht, hfull⟩ :=
    physicalFullAsymptoticLimitSet_tendsto_subseq μ β s hs
  refine ⟨x, hx, ?_⟩
  have hproject : Tendsto
      (fun j : ℕ => fullToScoreArray k
        (physicalFullOverlapLawArray μ β (s (t j))))
      atTop (𝓝 (fullToScoreArray k x)) :=
    ((fullToScoreArray_continuous k).tendsto x).comp hfull
  have hscore' : Tendsto
      (fun j : ℕ => fullToScoreArray k
        (physicalFullOverlapLawArray μ β (s (t j))))
      atTop (𝓝 y) := by
    simpa only [Function.comp_def, fullToScoreArray_physical]
      using hscore.comp ht.tendsto_atTop
  exact tendsto_nhds_unique hproject hscore'

end SlowEquilibration.PureCapturePhysicalAsymptoticFullLift
