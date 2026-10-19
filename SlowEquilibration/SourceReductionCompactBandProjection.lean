-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Topology.Maps.Proper.Basic

/-! The compact-projection argument used in manuscript Lemma `red-unions`:
a closed critical-center graph and a closed center/point band relation give
a closed random band-union graph, without any finiteness assumption. -/

@[expose] public section
namespace SlowEquilibration.SourceReductionCompactBandProjection

open Set

variable {D X U : Type*} [TopologicalSpace D] [TopologicalSpace X]
  [TopologicalSpace U] [CompactSpace U]

def bandUnionGraph (C : Set (D × U)) (B : Set (X × U)) : Set (D × X) :=
  {z | ∃ u, (z.1,u) ∈ C ∧ (z.2,u) ∈ B}

/-- Closed projection along the compact center space makes the union graph
closed even when a fiber of critical centers is empty or infinite. -/
theorem bandUnionGraph_isClosed {C : Set (D × U)} {B : Set (X × U)}
    (hC : IsClosed C) (hB : IsClosed B) :
    IsClosed (bandUnionGraph C B) := by
  let W : Set ((D × X) × U) :=
    {z | (z.1.1,z.2) ∈ C ∧ (z.1.2,z.2) ∈ B}
  have hW : IsClosed W := by
    apply IsClosed.inter
    · exact hC.preimage (continuous_fst.fst.prodMk continuous_snd)
    · exact hB.preimage (continuous_fst.snd.prodMk continuous_snd)
  have hp : IsClosed (Prod.fst '' W) :=
    isClosedMap_fst_of_compactSpace W hW
  convert hp using 1
  ext z
  constructor
  · rintro ⟨u, hu, hb⟩
    exact ⟨(z,u), ⟨hu,hb⟩, rfl⟩
  · rintro ⟨w, ⟨hu,hb⟩, hw⟩
    subst z
    exact ⟨w.2, hu, hb⟩

end SlowEquilibration.SourceReductionCompactBandProjection
