-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalFullFieldIdentity
public import SlowEquilibration.SphericalGibbsAllDimensions
public import SlowEquilibration.SphericalDisorderKernelMeasurable
public import SlowEquilibration.SphericalFieldKernelCongruence
public import SlowEquilibration.InformationFactorization
public import SlowEquilibration.ReductionJointInformation
public import SlowEquilibration.SphericalInitialRotation
public import SlowEquilibration.KernelTVMeasurable

/-! The manuscript's actual finite-dimensional polynomial field space.
Gibbs and physical transition kernels are Borel in the complete polynomial
field, via a constructed continuous coefficient section. Their equality
with the original tensor model is proved, including singular initial laws. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalFieldKernels

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalEffectiveField SphericalDynamics SphericalRotationCovariance
open SphericalAging.HardSphereDynamics ReductionJointInformation
open scoped Topology NNReal ENNReal ProbabilityTheory

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {N : ℕ}
attribute [local irreducible] mixedTransitionKernel

/-- Actual complete mixed polynomial fields, carrying their finite-dimensional norm topology. -/
abbrev Field (N : ℕ) (μ : FiniteMixture) :=
  FullSpace (N := N) (mixtureCoefficients μ)

abbrev fieldMap (μ : FiniteMixture) : Disorder N μ.maxDegree →L[ℝ] Field N μ :=
  project (mixtureCoefficients μ) (fieldBall N)

abbrev coefficientLift (μ : FiniteMixture) : Field N μ →L[ℝ] Disorder N μ.maxDegree :=
  lift (mixtureCoefficients μ) (fieldBall N)

abbrev fieldLaw (N : ℕ) (μ : FiniteMixture) : Measure (Field N μ) :=
  law (mixtureCoefficients μ) (fieldBall N)

@[simp] theorem fieldMap_coefficientLift (μ : FiniteMixture) (H : Field N μ) :
    fieldMap (N := N) μ (coefficientLift (N := N) μ H) = H := project_lift _ _ _

/-- Full polynomial identity, with no radial information lost. -/
theorem lifted_field_eq (μ : FiniteMixture) (J : Disorder N μ.maxDegree) :
    fieldOfMixture μ (coefficientLift (N := N) μ (fieldMap (N := N) μ J)) = fieldOfMixture μ J :=
  full_lift_project _ J

/-- The actual disorder-to-polynomial map has exactly the compressed Gaussian field law. -/
theorem fieldMap_hasLaw (μ : FiniteMixture) :
    HasLaw (fieldMap (N := N) μ) (fieldLaw N μ) (disorderLaw N μ.maxDegree) :=
  ⟨(fieldMap (N := N) μ).measurable.aemeasurable, rfl⟩

/-- Actual Gibbs law as a Borel probability kernel of the complete polynomial field. -/
def gibbsKernel (μ : FiniteMixture) (β : ℝ) : Kernel (Field N μ) (Vector N) :=
  (allDimensionGibbsKernel (N := N) (mixtureCoefficients μ) β).comap
    (coefficientLift (N := N) μ) (coefficientLift (N := N) μ).measurable

instance gibbsKernel_markov (μ : FiniteMixture) (β : ℝ) :
    IsMarkovKernel (gibbsKernel (N := N) μ β) := by
  unfold gibbsKernel
  infer_instance

@[simp] theorem gibbsKernel_apply (μ : FiniteMixture) (β : ℝ) (H : Field N μ) :
    gibbsKernel (N := N) μ β H = mixtureGibbsLaw μ β (coefficientLift (N := N) μ H) :=
by
  rw [gibbsKernel, Kernel.comap_apply, allDimensionGibbsKernel_apply]
  rfl

/-- No probability assertion is made for the canonical coefficient lift;
it represents exactly the original physical field instead. -/
theorem gibbsKernel_fieldMap (μ : FiniteMixture) (β : ℝ) (J : Disorder N μ.maxDegree) :
    gibbsKernel (N := N) μ β (fieldMap (N := N) μ J) = mixtureGibbsLaw μ β J := by
  rw [gibbsKernel_apply]
  change gibbsLaw N β (fieldOfMixture μ (coefficientLift (N := N) μ (fieldMap (N := N) μ J))) =
    gibbsLaw N β (fieldOfMixture μ J)
  rw [lifted_field_eq]

/-- Genuine physical conditional transition, Borel jointly in field and state. -/
def transitionKernel (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0) :
    Kernel (Field N μ × Vector N) (Vector N) :=
  (disorderTransitionKernel (N := N) μ β t).comap
    (fun z => (coefficientLift (N := N) μ z.1, z.2))
    (((coefficientLift (N := N) μ).measurable.comp measurable_fst).prodMk measurable_snd)

instance transitionKernel_markov (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0) :
    IsMarkovKernel (transitionKernel (N := N) μ β t) := by
  unfold transitionKernel
  infer_instance

@[simp] theorem transitionKernel_apply (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (H : Field N μ) (x : Vector N) :
    transitionKernel (N := N) μ β t (H,x) = mixedTransitionKernel μ (coefficientLift (N := N) μ H) β t x :=
by
  rw [transitionKernel, Kernel.comap_apply, disorderTransitionKernel_apply]

/-- Exact source-field factorization of the physical diffusion at each
spherical point; the statement is proved from field identity and the PDE. -/
theorem transitionKernel_fieldMap (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (J : Disorder N μ.maxDegree) (x : Vector N) (hx : OnSphere x) :
    transitionKernel (N := N) μ β t (fieldMap (N := N) μ J,x) = mixedTransitionKernel μ J β t x := by
  rw [transitionKernel_apply]
  exact mixedTransitionKernel_congr_onSphere hN μ _ J β
    (fun y _ => congrFun (lifted_field_eq μ J) y) t x hx

/-- The actual source mutual information uses H itself, rather than
stronger information about redundant raw Gaussian coefficients. -/
theorem information_identity (μ : FiniteMixture) (κ : Kernel (Field N μ) (Vector N)) [IsMarkovKernel κ] :
    endpointMutualInformation (disorderLaw N μ.maxDegree)
      (κ.comap (fieldMap (N := N) μ) (fieldMap (N := N) μ).measurable) =
    endpointMutualInformation (fieldLaw N μ) κ :=
  InformationFactorization.mutualInformation_of_measurable_factor _ _ (fieldMap (N := N) μ).measurable κ

theorem conditional_transitionKernel (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (H : Field N μ) :
    conditionalKernel (transitionKernel (N := N) μ β t) H =
      mixedTransitionKernel μ (coefficientLift (N := N) μ H) β t := by
  apply Kernel.ext
  intro x
  exact transitionKernel_apply μ β t H x

theorem evolvedKernel_apply_physical (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (κ : Kernel (Field N μ) (Vector N)) [IsMarkovKernel κ] (H : Field N μ) :
    evolvedKernel κ (transitionKernel (N := N) μ β t) H =
      mixedTransitionKernel μ (coefficientLift (N := N) μ H) β t ∘ₘ κ H := by
  rw [evolvedKernel_apply, conditional_transitionKernel]

/-- Exact equality with the original tensor process for every singular
initial law supported on the source sphere. -/
theorem evolvedKernel_fieldMap (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (κ : Kernel (Field N μ) (Vector N)) [IsMarkovKernel κ]
    (J : Disorder N μ.maxDegree)
    (hκ : ∀ᵐ x ∂κ (fieldMap (N := N) μ J), OnSphere x) :
    evolvedKernel κ (transitionKernel (N := N) μ β t) (fieldMap (N := N) μ J) =
      mixedTransitionKernel μ J β t ∘ₘ κ (fieldMap (N := N) μ J) := by
  rw [evolvedKernel_apply_physical]
  apply Measure.bind_congr_right
  filter_upwards [hκ] with x hx
  exact mixedTransitionKernel_congr_onSphere hN μ _ J β
    (fun y _ => congrFun (lifted_field_eq μ J) y) t x hx

/-- Literal physical endpoint distance, Borel in the actual complete field. -/
def endpointDistance (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (κ : Kernel (Field N μ) (Vector N)) (H : Field N μ) : ℝ :=
  totalVariation (evolvedKernel κ (transitionKernel (N := N) μ β T) H)
    (gibbsKernel (N := N) μ β H)

theorem endpointDistance_measurable (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (κ : Kernel (Field N μ) (Vector N)) [IsMarkovKernel κ] :
    Measurable (endpointDistance μ β T κ) :=
  KernelTVMeasurable.measurable_kernel_totalVariation _ _

/-- The exact infimum on the source's entire real time interval. -/
def intervalDistance (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (κ : Kernel (Field N μ) (Vector N)) (H : Field N μ) : ℝ :=
  sInf ((fun t : ℝ => totalVariation
    (mixedTransitionKernel μ (coefficientLift (N := N) μ H) β t.toNNReal ∘ₘ κ H)
    (gibbsKernel (N := N) μ β H)) '' Icc 0 (T:ℝ))

/-- The all-time infimum equals the endpoint through true physical
semigroup contraction and actual Gibbs stationarity. -/
theorem intervalDistance_eq_endpoint (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (κ : Kernel (Field N μ) (Vector N)) [IsMarkovKernel κ] (H : Field N μ) :
    intervalDistance μ β T κ H = endpointDistance μ β T κ H := by
  unfold intervalDistance endpointDistance
  rw [evolvedKernel_apply_physical, gibbsKernel_apply]
  simpa only [Real.toNNReal_coe] using
    mixed_totalVariation_endpoint_infimum hN μ (coefficientLift (N := N) μ H) β (κ H) T.coe_nonneg

theorem intervalDistance_measurable (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (κ : Kernel (Field N μ) (Vector N)) [IsMarkovKernel κ] :
    Measurable (intervalDistance μ β T κ) := by
  have he : intervalDistance μ β T κ = endpointDistance μ β T κ :=
    funext (intervalDistance_eq_endpoint hN μ β T κ)
  rw [he]
  exact endpointDistance_measurable μ β T κ

end SlowEquilibration.SphericalFieldKernels
