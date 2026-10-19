-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalFullToScore
public import SlowEquilibration.PureCaptureScorePrefixConsistency

/-! Asymptotic physical score-law cluster points. These are limits along
dimensions tending to infinity; finite-dimensional laws that occur in
the ordinary closure are deliberately excluded. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalAsymptoticScoreLimits

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCaptureOverlapScoreCoordinates
open PureCapturePhysicalScoreTightness
open PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalFullToScore
open PureCaptureScorePrefixConsistency
open PureCaptureConditionalCoarseWeakLimit
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- The cluster points of a sequence at infinity, characterized by
membership in the closures of every tail range. -/
def tailClusterSet {X : Type*} [TopologicalSpace X] (f : ℕ → X) : Set X :=
  ⋂ N, closure (f '' Ici N)

theorem mem_tailClusterSet_iff_mapClusterPt {X : Type*} [TopologicalSpace X]
    (f : ℕ → X) (x : X) :
    x ∈ tailClusterSet f ↔ MapClusterPt x atTop f := by
  simp only [tailClusterSet, mem_iInter]
  exact (mapClusterPt_atTop_iff_forall_mem_closure).symm

theorem tailClusterSet_closed {X : Type*} [TopologicalSpace X]
    (f : ℕ → X) : IsClosed (tailClusterSet f) := by
  unfold tailClusterSet
  exact isClosed_iInter (fun _ => isClosed_closure)

theorem tailClusterSet_subset_closure_range {X : Type*} [TopologicalSpace X]
    (f : ℕ → X) : tailClusterSet f ⊆ closure (Set.range f) := by
  intro x hx
  have hx0 : x ∈ closure (f '' Ici (0 : ℕ)) := by
    exact mem_iInter.mp hx 0
  apply closure_mono _ hx0
  rintro _ ⟨n, _, rfl⟩
  exact Set.mem_range.mpr ⟨n, rfl⟩

theorem tailClusterSet_compact {X : Type*} [TopologicalSpace X]
    (f : ℕ → X) (hcompact : IsCompact (closure (Set.range f))) :
    IsCompact (tailClusterSet f) :=
  hcompact.of_isClosed_subset (tailClusterSet_closed f)
    (tailClusterSet_subset_closure_range f)

def physicalScoreAsymptoticLimitSet (k : ℕ) (μ : FiniteMixture)
    (β : ℝ) : Set (ScoreLawArray k) :=
  tailClusterSet (annealedPhysicalScoreLawArray k μ β)

theorem physicalScoreAsymptoticLimitSet_compact (k : ℕ)
    (μ : FiniteMixture) (β : ℝ) :
    IsCompact (physicalScoreAsymptoticLimitSet k μ β) :=
  tailClusterSet_compact _ (physicalScoreLawArrayLimitSet_compact k μ β)

theorem physicalScoreAsymptoticLimitSet_subset (k : ℕ)
    (μ : FiniteMixture) (β : ℝ) :
    physicalScoreAsymptoticLimitSet k μ β ⊆
      physicalScoreLawArrayLimitSet k μ β :=
  tailClusterSet_subset_closure_range _

/-- Every strictly increasing sequence of physical dimensions has a
further subsequence converging to an asymptotic score-law limit. -/
theorem physicalScoreAsymptoticLimitSet_tendsto_subseq (k : ℕ)
    (μ : FiniteMixture) (β : ℝ) (s : ℕ → ℕ) (hs : StrictMono s) :
    ∃ limitArray ∈ physicalScoreAsymptoticLimitSet k μ β,
      ∃ t : ℕ → ℕ, StrictMono t ∧
        Tendsto (fun j : ℕ => annealedPhysicalScoreLawArray k μ β (s (t j)))
          atTop (𝓝 limitArray) := by
  obtain ⟨x, _, t, ht, hlim⟩ :=
    physicalScoreLawArrayLimitSet_tendsto_subseq k μ β s
  refine ⟨x, ?_, t, ht, hlim⟩
  apply (mem_tailClusterSet_iff_mapClusterPt _ _).2
  apply MapClusterPt.of_comp ((hs.comp ht).tendsto_atTop)
  exact hlim.mapClusterPt

/-- Corrected physical source-9.16 finite failure estimate: pointwise
companion extraction is required only on genuine n→∞ score-law cluster
points, never on fixed finite-dimensional Gibbs laws. -/
theorem expectedFiniteFailure_eventually_small_of_asymptotic_limits
    {k : ℕ} (μ : FiniteMixture) (β Q θ : ℝ)
    (hpoint : ∀ x ∈ physicalScoreAsymptoticLimitSet k μ β,
      Tendsto (fun T =>
        ((x T : Measure (ScoreCoordinates k T)) (scoreFailure Q θ)).toReal)
        atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T, ∀ᶠ n : ℕ in atTop,
      PureCapturePhysicalCoarseLimit.expectedFiniteFailure
        (n := n) (k := k) (T := T) μ β Q θ < ε := by
  let K := physicalScoreAsymptoticLimitSet k μ β
  let : CompactSpace K :=
    isCompact_iff_compactSpace.mp (physicalScoreAsymptoticLimitSet_compact k μ β)
  apply expectedFiniteFailure_eventually_small_of_compact_cluster_limits
    μ β Q θ (univ : Set K) isCompact_univ
    (fun T x => x.1 T)
    (fun T => (continuous_apply T).comp continuous_subtype_val)
    ?_ ?_ ?_ ε hε
  · intro s t hst x
    exact physicalScoreLawArrayLimitSet_failure_antitone μ β Q θ
      (physicalScoreAsymptoticLimitSet_subset k μ β x.2) hst
  · intro x _
    exact hpoint x.1 x.2
  · intro T s hs
    obtain ⟨L, hL, t, ht, hlim⟩ :=
      physicalScoreAsymptoticLimitSet_tendsto_subseq k μ β s hs
    refine ⟨⟨L, hL⟩, t, mem_univ _, ht, ?_⟩
    change Tendsto (fun m =>
      (annealedPhysicalScoreLawArray k μ β (s (t m))) T) atTop (𝓝 (L T))
    exact ((continuous_apply T).tendsto L).comp hlim

end SlowEquilibration.PureCapturePhysicalAsymptoticScoreLimits
