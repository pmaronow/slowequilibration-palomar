-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ReductionSupportedMenu

/-! Literal joint infimum and the arbitrary field-selected-weight and
field-selected-index consequences of source cor:red-selection. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ReductionFiniteMenu
open MeasureTheory ProbabilityTheory Set Filter
open ReductionJointInformation ReductionEndpointTransfer VaryingProbability
open scoped BigOperators ENNReal NNReal Topology ProbabilityTheory
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {ι X : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace X]

/-- The nested infimum is exactly the literal source joint infimum over
all simplex weights and all times in [0,T]. -/
theorem menuAllTimeDistance_eq_joint_inf (P : ℝ≥0 → Kernel X X)
    [∀ t, IsMarkovKernel (P t)] (ν : ι → Measure X) [∀ j, IsProbabilityMeasure (ν j)]
    (π : Measure X) [IsProbabilityMeasure π]
    (hcomp : ∀ s t, P (s+t)=P s ∘ₖ P t) (hinv : ∀ t, P t ∘ₘ π=π) (T : ℝ≥0) :
    menuAllTimeDistance P ν π T =
      sInf {r : ℝ | ∃ w : Weights ι, ∃ t : ℝ≥0, t ≤ T ∧ r=totalVariation (P t ∘ₘ mixture ν w) π} := by
  rw [menuAllTimeDistance_eq_endpoint P ν π hcomp hinv T]
  have hb : BddBelow {r : ℝ | ∃ w : Weights ι, ∃ t : ℝ≥0, t ≤ T ∧
      r=totalVariation (P t ∘ₘ mixture ν w) π} := by
    refine ⟨0,?_⟩
    rintro r ⟨w,t,ht,rfl⟩
    exact totalVariation_nonneg _ _
  have hne : ({r : ℝ | ∃ w : Weights ι, ∃ t : ℝ≥0, t ≤ T ∧
      r=totalVariation (P t ∘ₘ mixture ν w) π} : Set ℝ).Nonempty :=
    ⟨_,Classical.arbitrary (Weights ι),T,le_rfl,rfl⟩
  apply le_antisymm
  · apply le_csInf hne
    rintro r ⟨w,t,ht,rfl⟩
    have h := menuDistance_le (fun j => P T ∘ₘ ν j) π w
    rw [← evolve_mixture] at h
    exact h.trans (totalVariation_semigroup_antitone P (mixture ν w) π hcomp hinv ht)
  · apply le_ciInf
    intro w
    apply csInf_le hb
    exact ⟨w,T,le_rfl,by rw [evolve_mixture]⟩

theorem menuAllTimeDistance_le_weight (P : ℝ≥0 → Kernel X X)
    [∀ t, IsMarkovKernel (P t)] (ν : ι → Measure X) [∀ j, IsProbabilityMeasure (ν j)]
    (π : Measure X) [IsProbabilityMeasure π]
    (hcomp : ∀ s t, P (s+t)=P s ∘ₖ P t) (hinv : ∀ t, P t ∘ₘ π=π) (T : ℝ≥0)
    (w : Weights ι) :
    menuAllTimeDistance P ν π T ≤ allTimeDistance P (mixture ν w) π T := by
  rw [menuAllTimeDistance_eq_endpoint P ν π hcomp hinv T,
    allTimeDistance_eq_endpoint P _ π hcomp hinv T,evolve_mixture]
  exact menuDistance_le _ _ w

def vertexWeights (j : ι) : Weights ι := by
  classical
  exact ⟨Pi.single j 1,single_mem_stdSimplex ℝ j⟩

@[simp] theorem mixture_vertexWeights (ν : ι → Measure X) (j : ι) :
    mixture ν (vertexWeights j)=ν j := by
  classical
  simp [mixture,vertexWeights,Pi.single_apply,apply_ite,ite_smul]

theorem vertexWeights_measurable [MeasurableSpace ι] [MeasurableSingletonClass ι] :
    Measurable (vertexWeights : ι → Weights ι) := measurable_of_countable _

section Varying
variable {Ωₙ Xₙ ιₙ : ℕ → Type*}
  [∀ N, MeasurableSpace (Ωₙ N)] [∀ N, MeasurableSpace (Xₙ N)]
  [∀ N, Fintype (ιₙ N)] [∀ N, Nonempty (ιₙ N)]

/-- Every field-selected weight satisfies the all-time conclusion.
Measurable weights are genuine probability kernels by selectedKernel;
the pointwise uniform estimate actually covers arbitrary weights. -/
theorem selected_allTime_separation_of_uniform
    (d : ∀ N, Measure (Ωₙ N)) [∀ N, IsProbabilityMeasure (d N)]
    (ν : ∀ N, Ωₙ N → ιₙ N → Measure (Xₙ N)) [∀ N ω j, IsProbabilityMeasure (ν N ω j)]
    (π : ∀ N, Kernel (Ωₙ N) (Xₙ N)) [∀ N, IsMarkovKernel (π N)]
    (P : ∀ N, Ωₙ N → ℝ≥0 → Kernel (Xₙ N) (Xₙ N)) [∀ N ω t, IsMarkovKernel (P N ω t)]
    (hcomp : ∀ N ω s t, P N ω (s+t)=P N ω s ∘ₖ P N ω t)
    (hinv : ∀ N ω t, P N ω t ∘ₘ π N ω=π N ω)
    (T : ℕ → ℝ≥0) (w : ∀ N, Ωₙ N → Weights (ιₙ N))
    (hmenu : InProbability d (fun N ω => menuAllTimeDistance (P N ω) (ν N ω) (π N ω) (T N)) 1) :
    InProbability d (fun N ω => allTimeDistance (P N ω) (mixture (ν N ω) (w N ω)) (π N ω) (T N)) 1 := by
  apply inProbability_one_of_ge d _ _ hmenu
  · intro N ω
    exact menuAllTimeDistance_le_weight _ _ _ (hcomp N ω) (hinv N ω) _ _
  · intro N ω
    rw [allTimeDistance_eq_endpoint _ _ _ (hcomp N ω) (hinv N ω)]
    exact totalVariation_le_one _ _

/-- In particular an arbitrary field-dependent choice of one prescribed
law obeys the same all-time separation. -/
theorem selected_index_allTime_separation_of_uniform
    (d : ∀ N, Measure (Ωₙ N)) [∀ N, IsProbabilityMeasure (d N)]
    (ν : ∀ N, Ωₙ N → ιₙ N → Measure (Xₙ N)) [∀ N ω j, IsProbabilityMeasure (ν N ω j)]
    (π : ∀ N, Kernel (Ωₙ N) (Xₙ N)) [∀ N, IsMarkovKernel (π N)]
    (P : ∀ N, Ωₙ N → ℝ≥0 → Kernel (Xₙ N) (Xₙ N)) [∀ N ω t, IsMarkovKernel (P N ω t)]
    (hcomp : ∀ N ω s t, P N ω (s+t)=P N ω s ∘ₖ P N ω t)
    (hinv : ∀ N ω t, P N ω t ∘ₘ π N ω=π N ω)
    (T : ℕ → ℝ≥0) (j : ∀ N, Ωₙ N → ιₙ N)
    (hmenu : InProbability d (fun N ω => menuAllTimeDistance (P N ω) (ν N ω) (π N ω) (T N)) 1) :
    InProbability d (fun N ω => allTimeDistance (P N ω) (ν N ω (j N ω)) (π N ω) (T N)) 1 := by
  simpa only [mixture_vertexWeights] using
    selected_allTime_separation_of_uniform d ν π P hcomp hinv T (fun N ω => vertexWeights (j N ω)) hmenu

end Varying
end SlowEquilibration.ReductionFiniteMenu
