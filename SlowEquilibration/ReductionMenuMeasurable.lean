-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ReductionFiniteMenu
public import SlowEquilibration.ReductionJointInformation

/-! Joint Borel finite mixtures, their literal countable-infimum TV, and
arbitrary Borel field-selected weights. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ReductionFiniteMenu
open MeasureTheory ProbabilityTheory Set
open ReductionJointInformation
open scoped BigOperators ENNReal NNReal Topology ProbabilityTheory
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {ι Ω X : Type*} [Fintype ι] [MeasurableSpace Ω] [MeasurableSpace X]

theorem mixture_measurable (μ : Ω → ι → Measure X)
    (hμ : ∀ j, Measurable (fun ω => μ ω j))
    (w : Ω → Weights ι) (hw : Measurable w) :
    Measurable (fun ω => mixture (μ ω) (w ω)) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  simp_rw [mixture_apply]
  apply Finset.measurable_sum
  intro j _
  exact ((measurable_pi_apply j).comp (measurable_subtype_coe.comp hw)).ennreal_ofReal.mul
    ((Measure.measurable_coe hA).comp (hμ j))

theorem menuDistance_measurable [Nonempty ι] [MeasurableSpace.CountablyGenerated X]
    (μ : Ω → ι → Measure X) (π : Ω → Measure X)
    (hμ : ∀ j, Measurable (fun ω => μ ω j)) (hπ : Measurable π)
    [∀ ω j, IsProbabilityMeasure (μ ω j)] [∀ ω, IsProbabilityMeasure (π ω)] :
    Measurable (fun ω => menuDistance (μ ω) (π ω)) := by
  simp_rw [menuDistance_eq_countable_inf]
  apply Measurable.iInf
  intro k
  apply KernelTVMeasurable.measurable_totalVariation
  · exact mixture_measurable μ hμ _ measurable_const
  · exact hπ
  · intro ω
    infer_instance
  · intro ω
    infer_instance

/-- Actual probability kernel obtained by arbitrary Borel field-selected
weights on an arbitrary jointly measurable finite menu. -/
def selectedKernel (μ : ι → Kernel Ω X) (w : Ω → Weights ι) (hw : Measurable w) : Kernel Ω X where
  toFun ω := mixture (fun j => μ j ω) (w ω)
  measurable' := mixture_measurable _ (fun j => (μ j).measurable) w hw

instance selectedKernel_isMarkov (μ : ι → Kernel Ω X) [∀ j, IsMarkovKernel (μ j)]
    (w : Ω → Weights ι) (hw : Measurable w) : IsMarkovKernel (selectedKernel μ w hw) := by
  constructor
  intro ω
  exact mixture_probability _ _

theorem evolve_mixture (μ : ι → Measure X) (w : Weights ι) (K : Kernel X X) :
    K ∘ₘ mixture μ w = mixture (fun j => K ∘ₘ μ j) w := by
  classical
  unfold mixture
  have h (s : Finset ι) : K ∘ₘ (∑ j ∈ s, ENNReal.ofReal (w.1 j) • μ j) =
      ∑ j ∈ s, ENNReal.ofReal (w.1 j) • (K ∘ₘ μ j) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih => simp only [Finset.sum_insert hj,Measure.comp_add,Measure.comp_smul,ih]
  exact h Finset.univ

theorem evolved_selectedKernel (μ : ι → Kernel Ω X) [∀ j, IsMarkovKernel (μ j)]
    (w : Ω → Weights ι) (hw : Measurable w)
    (K : Kernel (Ω × X) X) [IsMarkovKernel K] (ω : Ω) :
    evolvedKernel (selectedKernel μ w hw) K ω =
      mixture (fun j => evolvedKernel (μ j) K ω) (w ω) := by
  rw [evolvedKernel_apply]
  change conditionalKernel K ω ∘ₘ mixture (fun j => μ j ω) (w ω) = _
  rw [evolve_mixture]
  congr 1
  funext j
  exact (evolvedKernel_apply (μ j) K ω).symm

theorem selected_conditionalMass_le_sum (μ : ι → Kernel Ω X) [∀ j, IsMarkovKernel (μ j)]
    (w : Ω → Weights ι) (hw : Measurable w)
    (K : Kernel (Ω × X) X) [IsMarkovKernel K] (B : Set (Ω × X)) (ω : Ω) :
    conditionalMass (selectedKernel μ w hw) K B ω ≤ ∑ j, conditionalMass (μ j) K B ω := by
  unfold conditionalMass
  rw [evolved_selectedKernel]
  exact mixture_mass_le_sum _ _ _

end SlowEquilibration.ReductionFiniteMenu
