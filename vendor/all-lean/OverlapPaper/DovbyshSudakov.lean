module

public import OverlapPaper.DSHilbertDirecting

@[expose] public section

/-! Dovbysh–Sudakov representation for an arbitrary positive-semidefinite,
weakly exchangeable diagonal-one array law. The directing law is constructed
from actual finite empirical Gram samples and is supported on the Hilbert ball. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace OverlapPaper
set_option maxHeartbeats 500000

def gramArrayProbability (ν : ProbabilityMeasure OverlapArray)
    (hG : (ν : Measure OverlapArray) GramArrays=1) : ProbabilityMeasure GramArray :=
  ⟨(ν : Measure OverlapArray).comap (Subtype.val : GramArray→OverlapArray),
    (MeasurableEmbedding.subtype_coe isClosed_GramArrays.measurableSet).isProbabilityMeasure_comap (by
      have hh : ∀ᵐR ∂(ν : Measure OverlapArray),R∈GramArrays :=
        (mem_ae_iff_prob_eq_one isClosed_GramArrays.measurableSet).mpr hG
      simpa only [Subtype.range_coe] using hh)⟩

theorem gramArrayProbability_map (ν : ProbabilityMeasure OverlapArray)
    (hG : (ν : Measure OverlapArray) GramArrays=1) :
    (gramArrayProbability ν hG).map (Subtype.val : GramArray→OverlapArray)=ν := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((ν : Measure OverlapArray).comap (Subtype.val : GramArray→OverlapArray)).map
    (Subtype.val : GramArray→OverlapArray)=(ν : Measure OverlapArray)
  rw [map_comap_subtype_coe isClosed_GramArrays.measurableSet]
  exact Measure.restrict_eq_self_of_ae_mem
    ((mem_ae_iff_prob_eq_one isClosed_GramArrays.measurableSet).mpr hG)

def HasDovbyshSudakovRepresentation (ν : ProbabilityMeasure OverlapArray) : Prop :=
  ∃Λ : ProbabilityMeasure (ProbabilityMeasure DSNormBall),ballOverlapSamplingProbability Λ=ν

theorem dovbysh_sudakov (ν : ProbabilityMeasure OverlapArray)
    (hG : (ν : Measure OverlapArray) GramArrays=1)
    (hν : WeaklyExchangeableOverlapLaw ν) : HasDovbyshSudakovRepresentation ν := by
  have hw : WeaklyExchangeableOverlapLaw
      ((gramArrayProbability ν hG).map (Subtype.val : GramArray→OverlapArray)) := by
    rw [gramArrayProbability_map]
    exact hν
  obtain ⟨Λ,hΛ⟩ := exists_hilbert_ball_directing_representation (gramArrayProbability ν hG) hw
  rw [gramArrayProbability_map] at hΛ
  exact ⟨Λ,hΛ⟩

end OverlapPaper
