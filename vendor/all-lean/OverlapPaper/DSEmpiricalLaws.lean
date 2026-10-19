module

public import OverlapPaper.DSGramEmpirical
public import OverlapPaper.DSDirectingCompact

@[expose] public section

/-! Actual random empirical directing measures associated with any law of
Gram arrays, and an actual convergent subsequence of their laws. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace OverlapPaper
set_option maxHeartbeats 300000

def gramEmpiricalDirectingPoint (n : ℕ) (R : GramArray) : DSDirectingSpace :=
  empiricalDirectingPoint (Nat.succ_pos n)
    (empiricalGramCoordinates (n+1) (Nat.succ_pos n) (1/(n+1:ℝ)) (by positivity) R)

theorem measurable_gramEmpiricalDirectingPoint (n : ℕ) :
    Measurable (gramEmpiricalDirectingPoint n) := by
  apply Measurable.comp (f := fun R : GramArray =>
    empiricalGramCoordinates (n+1) (Nat.succ_pos n) (1/(n+1:ℝ)) (by positivity) R)
    (measurable_empiricalDirectingPoint (Nat.succ_pos n))
  apply Measurable.of_eval
  intro i
  exact measurable_empiricalGramCoordinates (n+1) (Nat.succ_pos n) _ (by positivity) i

def gramEmpiricalDirectingLaw (ν : ProbabilityMeasure GramArray) (n : ℕ) :
    ProbabilityMeasure DSDirectingSpace := ν.map (gramEmpiricalDirectingPoint n)

theorem gramEmpiricalDirectingLaw_apply (ν : ProbabilityMeasure GramArray) (n : ℕ)
    (s : Set DSDirectingSpace) (hs : MeasurableSet s) :
    (gramEmpiricalDirectingLaw ν n : Measure DSDirectingSpace) s=
      (ν : Measure GramArray) (gramEmpiricalDirectingPoint n ⁻¹' s) :=
  Measure.map_apply (measurable_gramEmpiricalDirectingPoint n) hs

theorem gramEmpiricalDirectingLaw_compact_subsequence (ν : ProbabilityMeasure GramArray) :
    ∃ρ : ProbabilityMeasure DSDirectingSpace,∃φ : ℕ→ℕ,
      StrictMono φ ∧ Tendsto (gramEmpiricalDirectingLaw ν∘φ) atTop (𝓝 ρ) :=
  directing_laws_compact_subsequence (gramEmpiricalDirectingLaw ν)

end OverlapPaper
