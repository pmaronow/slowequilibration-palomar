-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ReductionInformationTransfer
public import SlowEquilibration.ReductionEndpointTransfer

/-! Source equal-mass and information transfer with the original sphere
support: no equal-mass assertion is required at off-sphere ambient points. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.ReductionInformationSupport

open MeasureTheory ProbabilityTheory Set Filter
open ReductionInformation ReductionJointInformation VaryingProbability
open scoped Topology NNReal ENNReal ProbabilityTheory

set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

/-- Equal averaged entry probability is needed only under the actual
initial marginal, permitting the source's spherical support condition. -/
theorem reference_mass_eq_of_ae_equal_mass (d : Measure Ω) [IsProbabilityMeasure d]
    (μ : Kernel Ω X) [IsMarkovKernel μ] (K : Kernel (Ω × X) X) [IsMarkovKernel K]
    {B : Set (Ω × X)} (hB : MeasurableSet B) {q : ℝ}
    (hequal : ∀ᵐ x ∂(μ ∘ₘ d),
      (∫ ω, (K (ω,x)).real (Prod.mk ω ⁻¹' B) ∂d) = q) :
    (retainedKernel K ∘ₘ (d.prod (μ ∘ₘ d))).real B = q := by
  have hi : Integrable (fun z : Ω × X => (retainedKernel K z).real B) (d.prod (μ ∘ₘ d)) := by
    apply Integrable.of_bound ((retainedKernel K).measurable_coe hB).ennreal_toReal.aestronglyMeasurable 1
    exact .of_forall (fun z => by
      change ‖(retainedKernel K z).real B‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one)
  have hcomp : (retainedKernel K ∘ₘ (d.prod (μ ∘ₘ d))).real B =
      ∫ z, (retainedKernel K z).real B ∂d.prod (μ ∘ₘ d) := by
    rw [Measure.real, Measure.bind_apply hB (retainedKernel K).aemeasurable,
      ← integral_toReal ((retainedKernel K).measurable_coe hB).aemeasurable
        (.of_forall (fun z => by finiteness))]
    rfl
  rw [hcomp, integral_prod_symm _ hi]
  calc
    _ = ∫ x, q ∂(μ ∘ₘ d) := by
      apply integral_congr_ae
      filter_upwards [hequal] with x hx
      simp only [Measure.real, retainedKernel_apply_set K hB]
      exact hx
    _ = q := by rw [integral_const, probReal_univ, one_smul]

/-- The source sphere support propagates to the actual averaged initial law. -/
theorem marginal_support (d : Measure Ω) (μ : Kernel Ω X)
    {S : Set X} (hS : MeasurableSet S) (hsupport : ∀ᵐ ω ∂d, ∀ᵐ x ∂μ ω, x ∈ S) :
    ∀ᵐ x ∂(μ ∘ₘ d), x ∈ S := Measure.ae_comp_of_ae_ae hS hsupport

variable {Ωs Xs : ℕ → Type*}
  [∀ N, MeasurableSpace (Ωs N)] [∀ N, MeasurableSpace (Xs N)]

/-- Full source information-to-entry-mass transfer with equal-mass only
on the support of the actual initial marginal. -/
theorem conditional_mass_inProbability_of_information
    (d : ∀ N, Measure (Ωs N)) [∀ N, IsProbabilityMeasure (d N)]
    (μ : ∀ N, Kernel (Ωs N) (Xs N)) [∀ N, IsMarkovKernel (μ N)]
    (K : ∀ N, Kernel (Ωs N × Xs N) (Xs N)) [∀ N, IsMarkovKernel (K N)]
    (B : ∀ N, Set (Ωs N × Xs N)) (hB : ∀ N, MeasurableSet (B N))
    (q : ℕ → ℝ) {C ζ : ℝ} (hC : 0 < C) (hζ : 0 < ζ)
    (hequal : ∀ N, ∀ᵐ x ∂(μ N ∘ₘ d N),
      (∫ ω, (K N (ω,x)).real (Prod.mk ω ⁻¹' B N) ∂d N) = q N)
    (hpoly : ∀ᶠ N : ℕ in atTop, q N ≤ C*(N : ℝ)^(-ζ))
    (hI : LittleLog (fun N => information (d N) (μ N))) :
    InProbability d (fun N => conditionalMass (μ N) (K N) (B N)) 0 := by
  let P (N : ℕ) : Measure (Ωs N × Xs N) := d N ⊗ₘ μ N
  let Q (N : ℕ) : Measure (Ωs N × Xs N) := (d N).prod ((μ N) ∘ₘ (d N))
  let R (N : ℕ) := retainedKernel (K N)
  let _ : ∀ N, IsProbabilityMeasure (P N) := fun N => inferInstance
  let _ : ∀ N, IsProbabilityMeasure (Q N) := fun N => inferInstance
  let _ : ∀ N, IsMarkovKernel (R N) := fun N => inferInstance
  have hpolyR : ∀ᶠ N in atTop, (R N ∘ₘ Q N).real (B N) ≤ C*(N : ℝ)^(-ζ) :=
    hpoly.mono (fun N hN => (reference_mass_eq_of_ae_equal_mass (d N) (μ N) (K N)
      (hB N) (hequal N)).le.trans hN)
  have hI' : LittleLog (fun N => InformationTheory.klDiv (P N) (Q N)) := hI
  have hp := event_mass_tendsto_zero_of_littleLog P Q R B hB hC hζ hpolyR hI'
  have hmean : Tendsto (fun N => ∫ ω, conditionalMass (μ N) (K N) (B N) ω ∂d N) atTop (𝓝 0) :=
    hp.congr' (.of_forall (fun N => retained_joint_mass_eq_integral (d N) (μ N) (K N) (hB N)))
  exact inProbability_zero_of_integral_tendsto_zero d _
    (fun N ω => measureReal_nonneg)
    (fun N => conditionalMass_integrable (d N) (μ N) (K N) (hB N)) hmean

/-- Source endpoint separation for ambient state spaces with initial
support on the sphere, using the precise AE equal-mass fact. -/
theorem information_endpoint_separation
    (d : ∀ N, Measure (Ωs N)) [∀ N, IsProbabilityMeasure (d N)]
    (μ π : ∀ N, Kernel (Ωs N) (Xs N))
    [∀ N, IsMarkovKernel (μ N)] [∀ N, IsMarkovKernel (π N)]
    (K : ∀ N, Kernel (Ωs N × Xs N) (Xs N)) [∀ N, IsMarkovKernel (K N)]
    (B : ∀ N, ℝ → Set (Ωs N × Xs N)) (hB : ∀ N M, MeasurableSet (B N M))
    (q : ℕ → ℝ → ℝ) {ζ : ℝ} (hζ : 0 < ζ)
    (hequal : ∀ M : ℝ, 0 < M → ∀ N, ∀ᵐ x ∂(μ N ∘ₘ d N),
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

end SlowEquilibration.ReductionInformationSupport
