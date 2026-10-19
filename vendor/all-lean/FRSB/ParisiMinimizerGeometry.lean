module
public import FRSB.ParisiMinimizer

@[expose] public section

/-! Geometry of the actual set of minimizing overlap measures. All convexity
and continuity inputs refer to the constructed PDE functional. -/
noncomputable section
open Set
namespace FRSB
open Paper

def IsParisiMinimizer (β h : ℝ) (μ : ParisiMeasure) : Prop :=
  ∀ ν : ParisiMeasure, parisiPDEFunctional β h μ ≤ parisiPDEFunctional β h ν

@[simp] theorem isParisiMinimizer_selected (β h : ℝ) :
    IsParisiMinimizer β h (parisiMinimizer β h) := parisiMinimizer_minimal β h

theorem isParisiMinimizer_iff_value (β h : ℝ) (μ : ParisiMeasure) :
    IsParisiMinimizer β h μ ↔
      parisiPDEFunctional β h μ = parisiPDEFunctional β h (parisiMinimizer β h) := by
  constructor
  · intro hμ
    exact le_antisymm (hμ _) (parisiMinimizer_minimal β h μ)
  · intro he ν
    rw [he]
    exact parisiMinimizer_minimal β h ν

theorem isParisiMinimizer_iff_infimum (β h : ℝ) (μ : ParisiMeasure) :
    IsParisiMinimizer β h μ ↔ parisiPDEFunctional β h μ = parisiPDEValue β h := by
  rw [isParisiMinimizer_iff_value, parisiMinimizer_value]

theorem isClosed_parisiMinimizers (β h : ℝ) :
    IsClosed {μ : ParisiMeasure | IsParisiMinimizer β h μ} := by
  have he : {μ : ParisiMeasure | IsParisiMinimizer β h μ} =
      {μ | parisiPDEFunctional β h μ = parisiPDEValue β h} := by
    ext μ
    exact isParisiMinimizer_iff_infimum β h μ
  rw [he]
  exact isClosed_eq (continuous_parisiPDEFunctional β h) continuous_const

theorem isCompact_parisiMinimizers (β h : ℝ) :
    IsCompact {μ : ParisiMeasure | IsParisiMinimizer β h μ} :=
  (isClosed_parisiMinimizers β h).isCompact

/-- Any mixture of actual minimizers is an actual minimizer. -/
theorem IsParisiMinimizer.mix {β h : ℝ} {μ ν : ParisiMeasure}
    (hμ : IsParisiMinimizer β h μ) (hν : IsParisiMinimizer β h ν)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    IsParisiMinimizer β h (parisiMix μ ν t) := by
  have he : parisiPDEFunctional β h μ = parisiPDEFunctional β h ν :=
    le_antisymm (hμ ν) (hν μ)
  intro σ
  have hc := parisiPDEFunctional_mix_le β h μ ν t ht
  rw [← he] at hc
  have hm := hμ σ
  nlinarith

/-- Two minimizing measures force equality in the exact measure-convexity
inequality for every probability mixture. -/
theorem IsParisiMinimizer.mix_value {β h : ℝ} {μ ν : ParisiMeasure}
    (hμ : IsParisiMinimizer β h μ) (hν : IsParisiMinimizer β h ν)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    parisiPDEFunctional β h (parisiMix μ ν t) =
      (1-t) * parisiPDEFunctional β h μ + t * parisiPDEFunctional β h ν := by
  have he : parisiPDEFunctional β h μ = parisiPDEFunctional β h ν :=
    le_antisymm (hμ ν) (hν μ)
  have hc := parisiPDEFunctional_mix_le β h μ ν t ht
  have hm := hμ (parisiMix μ ν t)
  rw [← he] at hc ⊢
  nlinarith

end FRSB
