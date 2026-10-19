-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalFieldKernels
public import SlowEquilibration.SphericalEqualMass

/-! Equal-mass and uniform entry probability for tests depending on the
complete polynomial field. Gaussian rotation and the physical kernel
factorization derive these identities on the original sphere. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalFieldKernels

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalEffectiveField SphericalDynamics SphericalRotationCovariance
open SphericalAging.HardSphereDynamics ReductionJointInformation
open scoped Topology NNReal ENNReal ProbabilityTheory

set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] mixedTransitionKernel

variable {N : ℕ}

/-- The literal test on raw tensor disorder, retaining only its full field. -/
def pullbackBand (μ : FiniteMixture) (B : Set (Field N μ × Vector N))
    (J : Disorder N μ.maxDegree) : Set (Vector N) :=
  Prod.mk (fieldMap (N := N) μ J) ⁻¹' B

theorem pullbackBand_measurable (μ : FiniteMixture)
    {B : Set (Field N μ × Vector N)} (hB : MeasurableSet B) :
    MeasurableSet {z : Disorder N μ.maxDegree × Vector N | z.2 ∈ pullbackBand μ B z.1} := by
  exact (((fieldMap (N := N) μ).measurable.comp measurable_fst).prodMk measurable_snd) hB

/-- The actual manuscript q: expected band entry from the uniform sphere law. -/
def uniformEntryMass (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (B : Set (Field N μ × Vector N)) : ℝ :=
  uniformExpectedEventMass μ β t (pullbackBand μ B)

/-- The averaged field-law point entry is exactly the raw tensor model
entry at every physical spherical point. -/
theorem mean_point_entry_eq_raw (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    {B : Set (Field N μ × Vector N)} (hB : MeasurableSet B)
    (x : Vector N) (hx : OnSphere x) :
    (∫ H, (transitionKernel (N := N) μ β t (H,x)).real (Prod.mk H ⁻¹' B) ∂fieldLaw N μ) =
      ∫ J, (mixedTransitionKernel μ J β t x).real (pullbackBand μ B J) ∂disorderLaw N μ.maxDegree := by
  have hm : Measurable (fun H : Field N μ =>
      (transitionKernel (N := N) μ β t (H,x)).real (Prod.mk H ⁻¹' B)) := by
    have hr := ((retainedKernel (transitionKernel (N := N) μ β t)).measurable_coe hB).ennreal_toReal
    have hr' := hr.comp (measurable_id.prodMk (measurable_const (a := x)))
    convert hr' using 1
    funext H
    simp only [Function.comp_apply, id_eq, Measure.real, retainedKernel_apply_set _ hB]
  change (∫ H, (transitionKernel (N := N) μ β t (H,x)).real (Prod.mk H ⁻¹' B)
    ∂(disorderLaw N μ.maxDegree).map (fieldMap (N := N) μ)) = _
  rw [integral_map (fieldMap (N := N) μ).measurable.aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  exact .of_forall fun J => by
    change (transitionKernel (N := N) μ β t (fieldMap (N := N) μ J,x)).real
      (Prod.mk (fieldMap (N := N) μ J) ⁻¹' B) =
        (mixedTransitionKernel μ J β t x).real (pullbackBand μ B J)
    rw [transitionKernel_fieldMap hN μ β t J x hx]
    rfl

/-- Genuine source equal-mass identity in the actual polynomial field space. -/
theorem point_entry_eq_uniform (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    {B : Set (Field N μ × Vector N)} (hB : MeasurableSet B)
    (hrot : ∀ (U : Vector N ≃ₗᵢ[ℝ] Vector N) J,
      pullbackBand μ B (rotatedDisorder U J) = U '' pullbackBand μ B J)
    (x : Vector N) (hx : OnSphere x) :
    (∫ H, (transitionKernel (N := N) μ β t (H,x)).real (Prod.mk H ⁻¹' B) ∂fieldLaw N μ) =
      uniformEntryMass μ β t B := by
  rw [mean_point_entry_eq_raw hN μ β t hB x hx]
  exact point_expected_mass_eq_uniform hN μ β t (pullbackBand μ B)
    (pullbackBand_measurable μ hB) hrot x hx

/-- The actual reference-law average is the original uniform entry q,
not a supplied error estimate or a surrogate initial marginal. -/
theorem uniform_conditional_mass_eq (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    {B : Set (Field N μ × Vector N)} (hB : MeasurableSet B) :
    (∫ H, conditionalMass (Kernel.const (Field N μ) (sphereLaw N))
      (transitionKernel (N := N) μ β t) B H ∂fieldLaw N μ) = uniformEntryMass μ β t B := by
  let _ := sphereLaw_probability N
  have hm := conditionalMass_measurable (Kernel.const (Field N μ) (sphereLaw N))
    (transitionKernel (N := N) μ β t) hB
  change (∫ H, conditionalMass (Kernel.const (Field N μ) (sphereLaw N))
    (transitionKernel (N := N) μ β t) B H
      ∂(disorderLaw N μ.maxDegree).map (fieldMap (N := N) μ)) = _
  rw [integral_map (fieldMap (N := N) μ).measurable.aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  exact .of_forall fun J => by
    change (evolvedKernel (Kernel.const (Field N μ) (sphereLaw N))
      (transitionKernel (N := N) μ β t) (fieldMap (N := N) μ J)).real
        (Prod.mk (fieldMap (N := N) μ J) ⁻¹' B) =
      (mixedTransitionKernel μ J β t ∘ₘ sphereLaw N).real (pullbackBand μ B J)
    rw [evolvedKernel_fieldMap hN μ β t _ J]
    · rfl
    · exact (sphereLaw_support hN).mono fun x hx => (onSphere_iff_norm_sq x).mpr hx

end SlowEquilibration.SphericalFieldKernels
