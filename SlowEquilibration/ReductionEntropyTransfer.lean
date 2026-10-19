-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ReductionEntropy
public import SlowEquilibration.ReductionEndpointTransfer

/-! Source `cor:red-entropy`: the exact capture and polynomial reference
entry premises imply separation for arbitrary field-dependent initial laws
whose actual conditional KL/log N vanishes only in probability. -/

@[expose] public section

noncomputable section
namespace SlowEquilibration.ReductionEntropyTransfer

open MeasureTheory ProbabilityTheory Set Filter
open ReductionJointInformation ReductionEntropy ReductionEndpointTransfer VaryingProbability
open scoped Topology NNReal ENNReal ProbabilityTheory

set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Ω X : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] [∀ N, MeasurableSpace (X N)]

theorem entropy_endpoint_separation
    (d : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (d N)]
    (μ π : ∀ N, Kernel (Ω N) (X N)) [∀ N, IsMarkovKernel (μ N)] [∀ N, IsMarkovKernel (π N)]
    (ν : ∀ N, Measure (X N)) [∀ N, IsProbabilityMeasure (ν N)]
    (K : ∀ N, Kernel (Ω N × X N) (X N)) [∀ N, IsMarkovKernel (K N)]
    (B : ∀ N, ℝ → Set (Ω N × X N)) (hB : ∀ N M, MeasurableSet (B N M))
    {ζ : ℝ} (hζ : 0 < ζ)
    (hpoly : ∀ M : ℝ, 0 < M → ∃ C : ℝ,
      ∀ᶠ N : ℕ in atTop,
        (∫ ω, conditionalMass (Kernel.const (Ω N) (ν N)) (K N) (B N M) ω ∂d N) ≤ C*(N : ℝ)^(-ζ))
    (hcapture : ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ᶠ N in atTop, (∫ ω, (π N ω).real (Prod.mk ω ⁻¹' B N M)ᶜ ∂d N) < η)
    (hI : LittleLogInProbability d (fun N ω => InformationTheory.klDiv (μ N ω) (ν N))) :
    InProbability d (fun N ω => totalVariation (evolvedKernel (μ N) (K N) ω) (π N ω)) 1 := by
  apply endpoint_separation_of_capture d μ π K B hB hcapture
  intro M hM
  obtain ⟨C,hpolyM⟩ := hpoly M hM
  exact conditional_mass_inProbability_of_entropy d μ ν K (fun N => B N M)
    (fun N => hB N M) hζ hpolyM hI

end SlowEquilibration.ReductionEntropyTransfer
