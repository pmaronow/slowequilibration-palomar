-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ReductionJointInformation
public import SlowEquilibration.VaryingProbability
public import SlowEquilibration.KernelTVMeasurable

/-! The measure-theoretic transfer in source `prop:red-information`, on
actual varying disorder spaces, initial probability kernels and conditional
transition kernels. Capture, polynomial q and the equal-mass Haar fact
are precisely the source premises; no separation conclusion is assumed. -/

@[expose] public section

noncomputable section
namespace SlowEquilibration.ReductionInformationTransfer

open MeasureTheory ProbabilityTheory Set Filter
open ReductionInformation ReductionJointInformation VaryingProbability
open scoped Topology NNReal ENNReal ProbabilityTheory

set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Ω X : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] [∀ N, MeasurableSpace (X N)]

/-- Actual mutual information between field and initial point controls
the conditional endpoint band mass in genuine varying-space probability. -/
theorem conditional_mass_inProbability_of_information
    (d : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (d N)]
    (μ : ∀ N, Kernel (Ω N) (X N)) [∀ N, IsMarkovKernel (μ N)]
    (K : ∀ N, Kernel (Ω N × X N) (X N)) [∀ N, IsMarkovKernel (K N)]
    (B : ∀ N, Set (Ω N × X N)) (hB : ∀ N, MeasurableSet (B N))
    (q : ℕ → ℝ) {C ζ : ℝ} (hC : 0 < C) (hζ : 0 < ζ)
    (hequal : ∀ N x, (∫ ω, (K N (ω,x)).real (Prod.mk ω ⁻¹' B N) ∂d N) = q N)
    (hpoly : ∀ᶠ N : ℕ in atTop, q N ≤ C*(N : ℝ)^(-ζ))
    (hI : LittleLog (fun N => information (d N) (μ N))) :
    InProbability d (fun N => conditionalMass (μ N) (K N) (B N)) 0 := by
  let P (N : ℕ) : Measure (Ω N × X N) := d N ⊗ₘ μ N
  let Q (N : ℕ) : Measure (Ω N × X N) := (d N).prod ((μ N) ∘ₘ (d N))
  let R (N : ℕ) := retainedKernel (K N)
  let _ : ∀ N, IsProbabilityMeasure (P N) := fun N => inferInstance
  let _ : ∀ N, IsProbabilityMeasure (Q N) := fun N => inferInstance
  let _ : ∀ N, IsMarkovKernel (R N) := fun N => inferInstance
  have hpolyR : ∀ᶠ N in atTop, (R N ∘ₘ Q N).real (B N) ≤ C*(N : ℝ)^(-ζ) :=
    hpoly.mono (fun N hN => (reference_mass_eq_of_equal_mass (d N) (μ N) (K N)
      (hB N) (hequal N)).le.trans hN)
  have hI' : LittleLog (fun N => InformationTheory.klDiv (P N) (Q N)) := hI
  have hp := event_mass_tendsto_zero_of_littleLog P Q R B hB hC hζ hpolyR hI'
  have hmean : Tendsto (fun N => ∫ ω, conditionalMass (μ N) (K N) (B N) ω ∂d N) atTop (𝓝 0) :=
    hp.congr' (.of_forall (fun N => retained_joint_mass_eq_integral (d N) (μ N) (K N) (hB N)))
  exact inProbability_zero_of_integral_tendsto_zero d _
    (fun N ω => measureReal_nonneg)
    (fun N => conditionalMass_integrable (d N) (μ N) (K N) (hB N)) hmean

/-- Full endpoint separation transfer under the source capture and
polynomial-q premises. For an actual stationary semigroup its all-time
infimum equals this endpoint distance by proved TV contraction. -/
theorem information_endpoint_separation
    (d : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (d N)]
    (μ π : ∀ N, Kernel (Ω N) (X N)) [∀ N, IsMarkovKernel (μ N)] [∀ N, IsMarkovKernel (π N)]
    (K : ∀ N, Kernel (Ω N × X N) (X N)) [∀ N, IsMarkovKernel (K N)]
    (B : ∀ N, ℝ → Set (Ω N × X N)) (hB : ∀ N M, MeasurableSet (B N M))
    (q : ℕ → ℝ → ℝ) {ζ : ℝ} (hζ : 0 < ζ)
    (hequal : ∀ M : ℝ, 0 < M → ∀ N x,
      (∫ ω, (K N (ω,x)).real (Prod.mk ω ⁻¹' B N M) ∂d N) = q N M)
    (hpoly : ∀ M : ℝ, 0 < M → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, q N M ≤ C*(N : ℝ)^(-ζ))
    (hcapture : ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ᶠ N in atTop,
        (∫ ω, (π N ω).real (Prod.mk ω ⁻¹' B N M)ᶜ ∂d N) < η)
    (hI : LittleLog (fun N => information (d N) (μ N))) :
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
  · intro M hM
    obtain ⟨C₀,hC₀,hpolyM⟩ := hpoly M hM
    exact conditional_mass_inProbability_of_information d μ K (fun N => B N M)
      (fun N => hB N M) (fun N => q N M) hC₀ hζ (hequal M hM) hpolyM hI
  · intro N M _ ω
    exact separation_from_event (evolvedKernel (μ N) (K N) ω) (π N ω)
      (measurable_prodMk_left (hB N M))

end SlowEquilibration.ReductionInformationTransfer
