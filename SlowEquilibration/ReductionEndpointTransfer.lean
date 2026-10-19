-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ReductionJointInformation
public import SlowEquilibration.VaryingProbability

/-! Actual endpoint-to-all-time and capture transfer on varying disorder
probability spaces. The endpoint band error is the genuine mass under the
evolved initial probability kernel. -/

@[expose] public section

noncomputable section
namespace SlowEquilibration.ReductionEndpointTransfer

open MeasureTheory ProbabilityTheory Set Filter
open ReductionJointInformation VaryingProbability
open scoped Topology NNReal ENNReal ProbabilityTheory

set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {α : Type*} [MeasurableSpace α]

def allTimeDistance (P : ℝ≥0 → Kernel α α) (μ π : Measure α) (T : ℝ≥0) : ℝ :=
  sInf ((fun t => totalVariation (P t ∘ₘ μ) π) '' Icc 0 T)

/-- The infimum over the whole source time interval is exactly its
endpoint TV, derived from actual stationary Markov-semigroup contraction. -/
theorem allTimeDistance_eq_endpoint (P : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (P t)]
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hcomp : ∀ s t, P (s+t) = P s ∘ₖ P t) (hinv : ∀ t, P t ∘ₘ π = π) (T : ℝ≥0) :
    allTimeDistance P μ π T = totalVariation (P T ∘ₘ μ) π := by
  have hne : (((fun t => totalVariation (P t ∘ₘ μ) π) '' Icc 0 T) : Set ℝ).Nonempty :=
    ⟨_, T, ⟨zero_le, le_rfl⟩, rfl⟩
  have hbelow : BddBelow ((fun t => totalVariation (P t ∘ₘ μ) π) '' Icc 0 T) := by
    refine ⟨0, ?_⟩
    rintro r ⟨t, _, rfl⟩
    exact totalVariation_nonneg _ _
  apply le_antisymm
  · exact csInf_le hbelow ⟨T, ⟨zero_le, le_rfl⟩, rfl⟩
  · apply le_csInf hne
    rintro r ⟨t, ht, rfl⟩
    exact totalVariation_semigroup_antitone P μ π hcomp hinv ht.2

variable {Ω X : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] [∀ N, MeasurableSpace (X N)]

/-- Exact source capture transfer with the genuine evolved band error.
The input error is produced by information, entropy or finite-menu tests;
the TV separation and the fixed-window selection are derived here. -/
theorem endpoint_separation_of_capture
    (d : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (d N)]
    (μ π : ∀ N, Kernel (Ω N) (X N)) [∀ N, IsMarkovKernel (μ N)] [∀ N, IsMarkovKernel (π N)]
    (K : ∀ N, Kernel (Ω N × X N) (X N)) [∀ N, IsMarkovKernel (K N)]
    (B : ∀ N, ℝ → Set (Ω N × X N)) (hB : ∀ N M, MeasurableSet (B N M))
    (hcapture : ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ᶠ N in atTop, (∫ ω, (π N ω).real (Prod.mk ω ⁻¹' B N M)ᶜ ∂d N) < η)
    (herror : ∀ M : ℝ, 0 < M →
      InProbability d (fun N => conditionalMass (μ N) (K N) (B N M)) 0) :
    InProbability d (fun N ω => totalVariation (evolvedKernel (μ N) (K N) ω) (π N ω)) 1 := by
  let C (N : ℕ) (M : ℝ) (ω : Ω N) := (π N ω).real (Prod.mk ω ⁻¹' B N M)ᶜ
  let E (N : ℕ) (M : ℝ) := conditionalMass (μ N) (K N) (B N M)
  apply VaryingProbability.testing_band_union d _ C E
  · intro N ω
    exact totalVariation_le_one _ _
  · intro N M _ ω
    exact measureReal_nonneg
  · intro N M _ ω
    exact measureReal_nonneg
  · intro N M _
    have hm : Measurable (C N M) :=
      (Kernel.measurable_kernel_prodMk_left (κ := π N) (hB N M).compl).ennreal_toReal
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    exact .of_forall (fun ω => by
      change ‖(π N ω).real (Prod.mk ω ⁻¹' B N M)ᶜ‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one)
  · exact hcapture
  · exact herror
  · intro N M _ ω
    exact separation_from_event (evolvedKernel (μ N) (K N) ω) (π N ω)
      (measurable_prodMk_left (hB N M))

end SlowEquilibration.ReductionEndpointTransfer
