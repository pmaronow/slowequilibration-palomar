-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ReductionInformation
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.MeasureTheory.Integral.Prod

/-! The actual field-retaining information comparison used in source
`prop:red-information`. Initial laws are genuine probability kernels and
may be singular. The reference law uses their actual average marginal;
retaining the field and evolving its genuine transition are explicit. -/

@[expose] public section

noncomputable section
namespace SlowEquilibration.ReductionJointInformation

open MeasureTheory ProbabilityTheory Set Filter
open ReductionInformation
open scoped Topology NNReal ENNReal ProbabilityTheory

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

def retainedKernel (K : Kernel (Ω × X) X) : Kernel (Ω × X) (Ω × X) :=
  Kernel.deterministic Prod.fst measurable_fst ×ₖ K

instance retainedKernel_isMarkov (K : Kernel (Ω × X) X) [IsMarkovKernel K] :
    IsMarkovKernel (retainedKernel K) := by
  unfold retainedKernel
  infer_instance

def conditionalKernel (K : Kernel (Ω × X) X) (ω : Ω) : Kernel X X :=
  K.comap (Prod.mk ω) (measurable_const.prodMk measurable_id)

instance conditionalKernel_isMarkov (K : Kernel (Ω × X) X) [IsMarkovKernel K] (ω : Ω) :
    IsMarkovKernel (conditionalKernel K ω) := by
  unfold conditionalKernel
  infer_instance

/-- The actual field-dependent initial kernel evolved by its actual
conditional transition. Measurability is provided by kernel composition. -/
def evolvedKernel (μ : Kernel Ω X) (K : Kernel (Ω × X) X) : Kernel Ω X :=
  (μ ⊗ₖ K).snd

instance evolvedKernel_isMarkov (μ : Kernel Ω X) [IsMarkovKernel μ]
    (K : Kernel (Ω × X) X) [IsMarkovKernel K] : IsMarkovKernel (evolvedKernel μ K) := by
  unfold evolvedKernel
  infer_instance

theorem evolvedKernel_apply (μ : Kernel Ω X) [IsMarkovKernel μ]
    (K : Kernel (Ω × X) X) [IsMarkovKernel K] (ω : Ω) :
    evolvedKernel μ K ω = conditionalKernel K ω ∘ₘ μ ω := by
  ext A hA
  rw [evolvedKernel, Kernel.snd_apply', Kernel.compProd_apply (measurable_snd hA),
    Measure.bind_apply hA (conditionalKernel K ω).aemeasurable]
  all_goals first | rfl | exact hA

theorem retainedKernel_apply_set (K : Kernel (Ω × X) X) [IsMarkovKernel K]
    {B : Set (Ω × X)} (hB : MeasurableSet B) (z : Ω × X) :
    retainedKernel K z B = K z (Prod.mk z.1 ⁻¹' B) := by
  rw [retainedKernel, Kernel.prod_apply, Kernel.deterministic_apply,
    Measure.dirac_prod]
  have hmk : Measurable (Prod.mk z.1 : X → Ω × X) := measurable_const.prodMk measurable_id
  exact Measure.map_apply hmk hB

/-- Evolving the joint initial law while retaining the field is exactly
the composition-product of disorder with the true evolved initial kernel. -/
theorem retained_joint_eq_compProd (d : Measure Ω) [IsProbabilityMeasure d]
    (μ : Kernel Ω X) [IsMarkovKernel μ] (K : Kernel (Ω × X) X) [IsMarkovKernel K] :
    retainedKernel K ∘ₘ (d ⊗ₘ μ) = d ⊗ₘ evolvedKernel μ K := by
  ext B hB
  rw [Measure.bind_apply hB (retainedKernel K).aemeasurable,
    Measure.lintegral_compProd ((retainedKernel K).measurable_coe hB),
    Measure.compProd_apply hB]
  simp_rw [retainedKernel_apply_set K hB, evolvedKernel_apply,
    Measure.bind_apply (measurable_prodMk_left hB) (conditionalKernel K _).aemeasurable]
  rfl

def conditionalMass (μ : Kernel Ω X) (K : Kernel (Ω × X) X)
    (B : Set (Ω × X)) (ω : Ω) : ℝ :=
  (evolvedKernel μ K ω).real (Prod.mk ω ⁻¹' B)

theorem conditionalMass_measurable (μ : Kernel Ω X) [IsMarkovKernel μ]
    (K : Kernel (Ω × X) X) [IsMarkovKernel K]
    {B : Set (Ω × X)} (hB : MeasurableSet B) : Measurable (conditionalMass μ K B) :=
  (Kernel.measurable_kernel_prodMk_left (κ := evolvedKernel μ K) hB).ennreal_toReal

theorem conditionalMass_integrable (d : Measure Ω) [IsProbabilityMeasure d]
    (μ : Kernel Ω X) [IsMarkovKernel μ] (K : Kernel (Ω × X) X) [IsMarkovKernel K]
    {B : Set (Ω × X)} (hB : MeasurableSet B) : Integrable (conditionalMass μ K B) d := by
  apply Integrable.of_bound (conditionalMass_measurable μ K hB).aestronglyMeasurable 1
  exact .of_forall (fun ω => by
    change ‖(evolvedKernel μ K ω).real (Prod.mk ω ⁻¹' B)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (measureReal_nonneg)]
    exact measureReal_le_one)

/-- Exact source identity p=E_H μ^H P^H(B(H)), using true disintegration. -/
theorem retained_joint_mass_eq_integral (d : Measure Ω) [IsProbabilityMeasure d]
    (μ : Kernel Ω X) [IsMarkovKernel μ] (K : Kernel (Ω × X) X) [IsMarkovKernel K]
    {B : Set (Ω × X)} (hB : MeasurableSet B) :
    (retainedKernel K ∘ₘ (d ⊗ₘ μ)).real B = ∫ ω, conditionalMass μ K B ω ∂d := by
  rw [retained_joint_eq_compProd, Measure.real, Measure.compProd_apply hB]
  rw [← integral_toReal (Kernel.measurable_kernel_prodMk_left
    (κ := evolvedKernel μ K) hB).aemeasurable (.of_forall (fun ω => by finiteness))]
  rfl

def information (d : Measure Ω) (μ : Kernel Ω X) : ℝ≥0∞ := endpointMutualInformation d μ

theorem retained_joint_entropy_le_information (d : Measure Ω) [IsProbabilityMeasure d]
    (μ : Kernel Ω X) [IsMarkovKernel μ] (K : Kernel (Ω × X) X) [IsMarkovKernel K] :
    InformationTheory.klDiv (retainedKernel K ∘ₘ (d ⊗ₘ μ))
      (retainedKernel K ∘ₘ (d.prod (μ ∘ₘ d))) ≤ information d μ :=
  relativeEntropy_kernel_contraction (d ⊗ₘ μ) (d.prod (μ ∘ₘ d)) (retainedKernel K)

private theorem kernel_comp_real (d : Measure Ω) [IsProbabilityMeasure d]
    (L : Kernel Ω X) [IsMarkovKernel L] {A : Set X} (hA : MeasurableSet A) :
    (L ∘ₘ d).real A = ∫ ω, (L ω).real A ∂d := by
  rw [Measure.real, Measure.bind_apply hA L.aemeasurable]
  rw [← integral_toReal (L.measurable_coe hA).aemeasurable (.of_forall (fun ω => by finiteness))]
  rfl

/-- Source equal-mass fact removes every dependence on the prescribed
initial marginal, including its singularity. The fact is the original
pointwise averaged band-entry premise proved by the Haar reduction. -/
theorem reference_mass_eq_of_equal_mass (d : Measure Ω) [IsProbabilityMeasure d]
    (μ : Kernel Ω X) [IsMarkovKernel μ] (K : Kernel (Ω × X) X) [IsMarkovKernel K]
    {B : Set (Ω × X)} (hB : MeasurableSet B) {q : ℝ}
    (hequal : ∀ x : X, (∫ ω, (K (ω,x)).real (Prod.mk ω ⁻¹' B) ∂d) = q) :
    (retainedKernel K ∘ₘ (d.prod (μ ∘ₘ d))).real B = q := by
  have hi : Integrable (fun z : Ω × X => (retainedKernel K z).real B) (d.prod (μ ∘ₘ d)) := by
    apply Integrable.of_bound ((retainedKernel K).measurable_coe hB).ennreal_toReal.aestronglyMeasurable 1
    exact .of_forall (fun z => by
      change ‖(retainedKernel K z).real B‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one)
  rw [kernel_comp_real (d.prod (μ ∘ₘ d)) (retainedKernel K) hB, integral_prod_symm _ hi]
  have hpoint (x : X) : (∫ ω, (retainedKernel K (ω,x)).real B ∂d) = q := by
    simp only [Measure.real, retainedKernel_apply_set K hB]
    exact hequal x
  simp_rw [hpoint]
  rw [integral_const, probReal_univ, one_smul]

end SlowEquilibration.ReductionJointInformation
