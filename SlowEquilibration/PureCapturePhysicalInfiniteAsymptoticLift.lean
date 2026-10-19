-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalInfiniteArrayTightness
public import SlowEquilibration.PureCapturePhysicalAsymptoticFullLift

/-! Genuine probability laws on the countably infinite physical overlap
array space along dimensions tending to infinity. Their finite marginals
are exactly the asymptotic full-array laws used in the coarse cover. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalInfiniteAsymptoticLift

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalInfiniteArrayTightness
open PureCapturePhysicalAsymptoticScoreLimits
open PureCapturePhysicalAsymptoticFullLift
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def physicalInfiniteAsymptoticLimitSet
    (μ : FiniteMixture) (β : ℝ) :
    Set (ProbabilityMeasure InfiniteOverlapCoordinates) :=
  tailClusterSet (fun n => physicalPaddedFullOverlapLaw n μ β)

theorem physicalInfiniteAsymptoticLimitSet_compact
    (μ : FiniteMixture) (β : ℝ) :
    IsCompact (physicalInfiniteAsymptoticLimitSet μ β) :=
  tailClusterSet_compact _ (physicalPaddedFullOverlapLaws_compact_closure μ β)

theorem physicalInfiniteAsymptoticLimitSet_tendsto_subseq
    (μ : FiniteMixture) (β : ℝ)
    (s : ℕ → ℕ) (hs : StrictMono s) :
    ∃ ρ ∈ physicalInfiniteAsymptoticLimitSet μ β,
      ∃ t : ℕ → ℕ, StrictMono t ∧
        Tendsto (fun j => physicalPaddedFullOverlapLaw (s (t j)) μ β)
          atTop (𝓝 ρ) := by
  obtain ⟨ρ, _, t, ht, hlim⟩ :=
    physicalPaddedFullOverlapLaws_tendsto_subseq μ β s
  refine ⟨ρ, ?_, t, ht, hlim⟩
  apply (mem_tailClusterSet_iff_mapClusterPt _ _).2
  apply MapClusterPt.of_comp ((hs.comp ht).tendsto_atTop)
  exact hlim.mapClusterPt

theorem infiniteToFullLawArray_maps_asymptotic_limits
    (μ : FiniteMixture) (β : ℝ)
    {ρ : ProbabilityMeasure InfiniteOverlapCoordinates}
    (hρ : ρ ∈ physicalInfiniteAsymptoticLimitSet μ β) :
    infiniteToFullLawArray ρ ∈ physicalFullAsymptoticLimitSet μ β := by
  have hcluster : MapClusterPt ρ atTop
      (fun n => physicalPaddedFullOverlapLaw n μ β) :=
    (mem_tailClusterSet_iff_mapClusterPt _ _).1 hρ
  obtain ⟨s, hs, hinfinite⟩ := hcluster.tendsto_subseq
  have hfull := fullOverlapLawArray_tendsto_of_padded_tendsto
    μ β s hs.tendsto_atTop hinfinite
  apply (mem_tailClusterSet_iff_mapClusterPt _ _).2
  have hmap : MapClusterPt (infiniteToFullLawArray ρ) atTop
      ((physicalFullOverlapLawArray μ β) ∘ s) := by
    simpa only [Function.comp_def] using hfull.mapClusterPt
  exact MapClusterPt.of_comp hs.tendsto_atTop hmap

/-- Every genuine asymptotic physical full-array limit is the system of
finite marginals of one genuine probability measure on countably infinite
overlap matrices. This produces the exact law type required by the
Dovbysh--Sudakov theorem. -/
theorem fullAsymptoticLimit_exists_infiniteLimit
    (μ : FiniteMixture) (β : ℝ)
    {x : FullOverlapLawArray}
    (hx : x ∈ physicalFullAsymptoticLimitSet μ β) :
    ∃ ρ ∈ physicalInfiniteAsymptoticLimitSet μ β,
      infiniteToFullLawArray ρ = x := by
  obtain ⟨s, hs, hfull⟩ :=
    ((mem_tailClusterSet_iff_mapClusterPt _ _).1 hx).tendsto_subseq
  obtain ⟨ρ, hρ, t, ht, hinfinite⟩ :=
    physicalInfiniteAsymptoticLimitSet_tendsto_subseq μ β s hs
  refine ⟨ρ, hρ, ?_⟩
  have hproject := fullOverlapLawArray_tendsto_of_padded_tendsto
    μ β (s ∘ t) (hs.comp ht).tendsto_atTop hinfinite
  have hfull' : Tendsto
      (fun j => physicalFullOverlapLawArray μ β (s (t j)))
      atTop (𝓝 x) := by
    simpa only [Function.comp_def] using hfull.comp ht.tendsto_atTop
  have hproject' : Tendsto
      (fun j => physicalFullOverlapLawArray μ β (s (t j)))
      atTop (𝓝 (infiniteToFullLawArray ρ)) := by
    simpa only [Function.comp_def] using hproject
  exact tendsto_nhds_unique hproject' hfull'

theorem physicalInfiniteAsymptoticLimitSet_image_full
    (μ : FiniteMixture) (β : ℝ) :
    infiniteToFullLawArray '' physicalInfiniteAsymptoticLimitSet μ β =
      physicalFullAsymptoticLimitSet μ β := by
  apply Set.Subset.antisymm
  · rintro x ⟨ρ, hρ, rfl⟩
    exact infiniteToFullLawArray_maps_asymptotic_limits μ β hρ
  · intro x hx
    obtain ⟨ρ, hρ, hr⟩ :=
      fullAsymptoticLimit_exists_infiniteLimit μ β hx
    exact ⟨ρ, hρ, hr⟩

end SlowEquilibration.PureCapturePhysicalInfiniteAsymptoticLift
