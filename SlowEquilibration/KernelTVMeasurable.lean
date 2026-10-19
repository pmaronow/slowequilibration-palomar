-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.Separation
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
public import Mathlib.MeasureTheory.SetAlgebra
public import Mathlib.Probability.Kernel.Basic

/-! Actual total variation is measurable for probability-measure families
on countably generated measurable spaces, including Euclidean Borel spaces.
The event supremum is identified with a fixed countable generating algebra
by genuine symmetric-difference approximation in the sum measure. -/

@[expose] public section

noncomputable section
namespace SlowEquilibration.KernelTVMeasurable

open MeasureTheory ProbabilityTheory MeasurableSpace Set
open scoped Topology ENNReal NNReal symmDiff

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
variable [CountablyGenerated α]

/-- One fixed countable algebra, independent of the probability measures. -/
def eventAlgebra (α : Type*) [MeasurableSpace α] [CountablyGenerated α] : Set (Set α) :=
  generateSetAlgebra (countableGeneratingSet α)

lemma eventAlgebra_isAlgebra : IsSetAlgebra (eventAlgebra α) :=
  isSetAlgebra_generateSetAlgebra

lemma eventAlgebra_countable : (eventAlgebra α).Countable :=
  countable_generateSetAlgebra (countable_countableGeneratingSet (α := α))

instance eventAlgebra_countable_index : Countable (eventAlgebra α) :=
  eventAlgebra_countable.to_subtype

instance eventAlgebra_nonempty_index : Nonempty (eventAlgebra α) :=
  ⟨⟨∅, eventAlgebra_isAlgebra.empty_mem⟩⟩

lemma eventAlgebra_generates : generateFrom (eventAlgebra α) = (inferInstance : MeasurableSpace α) := by
  rw [eventAlgebra, generateFrom_generateSetAlgebra_eq, generateFrom_countableGeneratingSet]

lemma eventAlgebra_measurable {A : Set α} (hA : A ∈ eventAlgebra α) : MeasurableSet A := by
  change A ∈ generateSetAlgebra (countableGeneratingSet α) at hA
  induction hA using generateSetAlgebra_induction with
  | base A hA => exact measurableSet_countableGeneratingSet hA
  | empty => exact MeasurableSet.empty
  | compl A _ hA => exact hA.compl
  | union A B _ _ hA hB => exact hA.union hB

private lemma event_difference_approximation (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : Set α} (hB : MeasurableSet B) {ε : ℝ} (hε : 0 < ε) :
    ∃ A ∈ eventAlgebra α,
      |μ.real B - ν.real B| ≤ |μ.real A - ν.real A| + ε := by
  have hcover : ∃ D : Set (Set α), D.Countable ∧ D ⊆ eventAlgebra α ∧ (μ+ν) (⋃₀ D)ᶜ = 0 := by
    refine ⟨{univ}, countable_singleton _, ?_, by simp⟩
    intro A hA
    obtain rfl := mem_singleton_iff.mp hA
    exact eventAlgebra_isAlgebra.univ_mem
  obtain ⟨A, hA, happrox⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    (μ := μ+ν) eventAlgebra_isAlgebra.isSetRing hcover eventAlgebra_generates.symm hB
    (ENNReal.ofReal_pos.mpr hε)
  have hsmall : (μ+ν).real (A ∆ B) < ε := by
    have hh := (ENNReal.toReal_lt_toReal (by finiteness : (μ+ν) (A ∆ B) ≠ ∞)
      ENNReal.ofReal_ne_top).mpr happrox
    simpa only [Measure.real, ENNReal.toReal_ofReal hε.le] using hh
  have hμ := abs_measureReal_sub_le_measureReal_symmDiff
    (μ := μ) hB.nullMeasurableSet (eventAlgebra_measurable hA).nullMeasurableSet
  have hν := abs_measureReal_sub_le_measureReal_symmDiff
    (μ := ν) (eventAlgebra_measurable hA).nullMeasurableSet hB.nullMeasurableSet
  rw [symmDiff_comm B A] at hμ
  have htri : |μ.real B - ν.real B| ≤
      |μ.real B - μ.real A| + |μ.real A - ν.real A| + |ν.real A - ν.real B| := by
    calc
      _ = |(μ.real B - μ.real A) + (μ.real A - ν.real A) + (ν.real A - ν.real B)| := by congr 1; ring
      _ ≤ |(μ.real B - μ.real A) + (μ.real A - ν.real A)| + |ν.real A - ν.real B| := abs_add_le _ _
      _ ≤ _ := by
        have hh := abs_add_le (μ.real B - μ.real A) (μ.real A - ν.real A)
        linarith
  rw [measureReal_add_apply] at hsmall
  exact ⟨A, hA, by linarith⟩

/-- The actual total-variation event supremum is a fixed countable
supremum. The algebra does not depend on μ or ν. -/
theorem totalVariation_eq_countable_sup (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    totalVariation μ ν = ⨆ A : eventAlgebra α, |μ.real A.1 - ν.real A.1| := by
  have hbound : BddAbove (range (fun A : eventAlgebra α => |μ.real A.1 - ν.real A.1|)) := by
    refine ⟨totalVariation μ ν, ?_⟩
    rintro r ⟨A, rfl⟩
    exact event_difference_le_totalVariation μ ν (eventAlgebra_measurable A.2)
  apply le_antisymm
  · apply csSup_le
    · exact ⟨0, ∅, MeasurableSet.empty, by simp⟩
    · rintro r ⟨B, hB, rfl⟩
      apply le_of_forall_pos_le_add
      intro ε hε
      obtain ⟨A, hA, happrox⟩ := event_difference_approximation μ ν hB hε
      have hsup := le_ciSup hbound (⟨A,hA⟩ : eventAlgebra α)
      linarith
  · apply ciSup_le
    intro A
    exact event_difference_le_totalVariation μ ν (eventAlgebra_measurable A.2)

/-- Jointly measurable actual probability-measure families have measurable
actual total variation in the manuscript's event normalization. -/
theorem measurable_totalVariation (μ ν : Ω → Measure α) (hμ : Measurable μ) (hν : Measurable ν)
    (hμprob : ∀ x, IsProbabilityMeasure (μ x)) (hνprob : ∀ x, IsProbabilityMeasure (ν x)) :
    Measurable (fun x => totalVariation (μ x) (ν x)) := by
  have he : (fun x => totalVariation (μ x) (ν x)) =
      (fun x => ⨆ A : eventAlgebra α, |(μ x).real A.1 - (ν x).real A.1|) := by
    funext x
    let _ := hμprob x
    let _ := hνprob x
    exact totalVariation_eq_countable_sup (μ x) (ν x)
  rw [he]
  apply Measurable.iSup
  intro A
  have hm : Measurable (fun x => (μ x).real A.1) :=
    ENNReal.measurable_toReal.comp ((Measure.measurable_coe (eventAlgebra_measurable A.2)).comp hμ)
  have hn : Measurable (fun x => (ν x).real A.1) :=
    ENNReal.measurable_toReal.comp ((Measure.measurable_coe (eventAlgebra_measurable A.2)).comp hν)
  exact continuous_abs.measurable.comp (hm.sub hn)

theorem measurable_kernel_totalVariation (K L : Kernel Ω α) [IsMarkovKernel K] [IsMarkovKernel L] :
    Measurable (fun x => totalVariation (K x) (L x)) :=
  measurable_totalVariation K L K.measurable L.measurable (fun _ => inferInstance) (fun _ => inferInstance)

theorem measurable_kernel_totalVariation_const (K : Kernel Ω α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] : Measurable (fun x => totalVariation (K x) π) :=
  measurable_totalVariation K (fun _ => π) K.measurable measurable_const
    (fun _ => inferInstance) (fun _ => inferInstance)

theorem measurableSet_kernel_totalVariation_le (K L : Kernel Ω α)
    [IsMarkovKernel K] [IsMarkovKernel L] (r : ℝ) :
    MeasurableSet {x | totalVariation (K x) (L x) ≤ r} :=
  measurableSet_le (measurable_kernel_totalVariation K L) measurable_const

theorem measurableSet_kernel_totalVariation_lt (K L : Kernel Ω α)
    [IsMarkovKernel K] [IsMarkovKernel L] (r : ℝ) :
    MeasurableSet {x | totalVariation (K x) (L x) < r} :=
  measurableSet_lt (measurable_kernel_totalVariation K L) measurable_const

end SlowEquilibration.KernelTVMeasurable
