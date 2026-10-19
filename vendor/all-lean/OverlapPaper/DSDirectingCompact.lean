module

public import OverlapPaper.DSDirectingTopology
public import Mathlib.Topology.Sequences

@[expose] public section

/-! Actual compactness of laws of random directing measures in the weak
Borel model. This is the probability-measure compactness input to DS. -/
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology
namespace OverlapPaper

instance : SeparableSpace DSDirectingSpace :=
  isSeparable_univ_iff.mp isCompact_univ.isSeparable

instance : SecondCountableTopology DSDirectingSpace := by
  letI : MetricSpace DSDirectingSpace := TopologicalSpace.metrizableSpaceMetric DSDirectingSpace
  infer_instance

theorem directing_laws_compact_subsequence (ρ : ℕ→ProbabilityMeasure DSDirectingSpace) :
    ∃ ρlim : ProbabilityMeasure DSDirectingSpace,∃φ : ℕ→ℕ,
      StrictMono φ ∧ Tendsto (ρ∘φ) atTop (𝓝 ρlim) :=
  CompactSpace.tendsto_subseq ρ

end OverlapPaper
