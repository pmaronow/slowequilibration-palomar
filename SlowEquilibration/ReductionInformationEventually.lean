-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ReductionInformationSupport

/-! The exact eventual-dimension quantifiers of the manuscript's
information reduction. No assertion at unused small dimensions is needed. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.ReductionInformationEventually

open MeasureTheory ProbabilityTheory Set Filter
open ReductionInformation ReductionJointInformation VaryingProbability
open scoped Topology NNReal ENNReal ProbabilityTheory

set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Ω X : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] [∀ N, MeasurableSpace (X N)]

/-- Actual endpoint entry tends to zero when the source equal-mass
identity and polynomial bound hold at all sufficiently large dimensions. -/
theorem conditional_mass_inProbability_of_information
    (d : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (d N)]
    (μ : ∀ N, Kernel (Ω N) (X N)) [∀ N, IsMarkovKernel (μ N)]
    (K : ∀ N, Kernel (Ω N × X N) (X N)) [∀ N, IsMarkovKernel (K N)]
    (B : ∀ N, Set (Ω N × X N)) (hB : ∀ N, MeasurableSet (B N))
    (q : ℕ → ℝ) {C ζ : ℝ} (hC : 0 < C) (hζ : 0 < ζ)
    (hequal : ∀ᶠ N in atTop, ∀ᵐ x ∂(μ N ∘ₘ d N),
      (∫ ω, (K N (ω,x)).real (Prod.mk ω ⁻¹' B N) ∂d N) = q N)
    (hpoly : ∀ᶠ N : ℕ in atTop, q N ≤ C*(N : ℝ)^(-ζ))
    (hI : LittleLog (fun N => information (d N) (μ N))) :
    InProbability d (fun N => conditionalMass (μ N) (K N) (B N)) 0 := by
  let P (N : ℕ) : Measure (Ω N × X N) := d N ⊗ₘ μ N
  let Q (N : ℕ) : Measure (Ω N × X N) := (d N).prod ((μ N) ∘ₘ (d N))
  let R (N : ℕ) := retainedKernel (K N)
  let _ : ∀ N, IsProbabilityMeasure (P N) := fun N => inferInstance
  let _ : ∀ N, IsProbabilityMeasure (Q N) := fun N => inferInstance
  let _ : ∀ N, IsMarkovKernel (R N) := fun N => inferInstance
  have hpolyR : ∀ᶠ N in atTop, (R N ∘ₘ Q N).real (B N) ≤ C*(N : ℝ)^(-ζ) := by
    filter_upwards [hequal,hpoly] with N he hp
    exact (ReductionInformationSupport.reference_mass_eq_of_ae_equal_mass
      (d N) (μ N) (K N) (hB N) he).le.trans hp
  have hI' : LittleLog (fun N => InformationTheory.klDiv (P N) (Q N)) := hI
  have hp := event_mass_tendsto_zero_of_littleLog P Q R B hB hC hζ hpolyR hI'
  have hmean : Tendsto (fun N => ∫ ω, conditionalMass (μ N) (K N) (B N) ω ∂d N) atTop (𝓝 0) :=
    hp.congr' (.of_forall (fun N => retained_joint_mass_eq_integral (d N) (μ N) (K N) (hB N)))
  exact inProbability_zero_of_integral_tendsto_zero d _
    (fun N ω => measureReal_nonneg)
    (fun N => conditionalMass_integrable (d N) (μ N) (K N) (hB N)) hmean

/-- Full endpoint separation with the original fixed-window capture and
polynomial q premises, allowing the precise eventual source dimensions. -/
theorem information_endpoint_separation
    (d : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (d N)]
    (μ π : ∀ N, Kernel (Ω N) (X N)) [∀ N, IsMarkovKernel (μ N)] [∀ N, IsMarkovKernel (π N)]
    (K : ∀ N, Kernel (Ω N × X N) (X N)) [∀ N, IsMarkovKernel (K N)]
    (B : ∀ N, ℝ → Set (Ω N × X N)) (hB : ∀ N M, MeasurableSet (B N M))
    (q : ℕ → ℝ → ℝ) {ζ : ℝ} (hζ : 0 < ζ)
    (hequal : ∀ M : ℝ, 0 < M → ∀ᶠ N in atTop, ∀ᵐ x ∂(μ N ∘ₘ d N),
      (∫ ω, (K N (ω,x)).real (Prod.mk ω ⁻¹' B N M) ∂d N) = q N M)
    (hpoly : ∀ M : ℝ, 0 < M → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, q N M ≤ C*(N : ℝ)^(-ζ))
    (hcapture : ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ᶠ N in atTop, (∫ ω, (π N ω).real (Prod.mk ω ⁻¹' B N M)ᶜ ∂d N) < η)
    (hI : LittleLog (fun N => information (d N) (μ N))) :
    InProbability d (fun N ω => totalVariation (evolvedKernel (μ N) (K N) ω) (π N ω)) 1 := by
  apply ReductionEndpointTransfer.endpoint_separation_of_capture d μ π K B hB hcapture
  intro M hM
  obtain ⟨C,hC,hpolyM⟩ := hpoly M hM
  exact conditional_mass_inProbability_of_information d μ K (fun N => B N M)
    (fun N => hB N M) (fun N => q N M) hC hζ (hequal M hM) hpolyM hI

/-- Changing finitely many dimensions does not change convergence in probability. -/
theorem inProbability_congr_eventually (d : ∀ N, Measure (Ω N))
    (f g : ∀ N, Ω N → ℝ) (c : ℝ) (hfg : ∀ᶠ N in atTop, ∀ ω, f N ω=g N ω)
    (hf : InProbability d f c) : InProbability d g c := by
  intro ε hε
  apply (hf ε hε).congr'
  filter_upwards [hfg] with N hN
  congr 1
  ext ω
  change (ε ≤ ‖f N ω-c‖) ↔ (ε ≤ ‖g N ω-c‖)
  rw [hN ω]

end SlowEquilibration.ReductionInformationEventually
