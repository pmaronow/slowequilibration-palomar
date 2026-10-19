-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalFullFieldPathKernel

@[expose] public section

/-! # Intrinsic sphere total variation for arbitrary full-field initial kernels

The initial law is literally an arbitrary Borel probability kernel into
the sphere, and may be singular. Both evolved law and Gibbs law are sphere
measures. Their intrinsic event-supremum distance agrees with the faithful
ambient physical distance, which provides the whole-time endpoint identity.
-/

namespace SlowEquilibration.SphericalFullFieldSphereTV
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalDynamics SphericalRotationCovariance SphericalFieldKernels SphericalReversibility
open SphericalFullFieldPathKernel ReductionJointInformation
open SphericalAging.HardSphereDynamics
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

def sphereBasepoint (hN : 1 ≤ N) : PhysicalSphere N := by
  have hnon : Nonempty (PhysicalSphere N) := by
    obtain ⟨x,hx⟩ := (sphereLaw_support hN).exists
    exact ⟨⟨x,(onSphere_iff_norm_sq x).mpr hx⟩⟩
  exact Classical.choice hnon

def sphereStateRecovery (x₀ : PhysicalSphere N) (x : Vector N) : PhysicalSphere N := by
  classical
  exact if hx : OnSphere x then ⟨x,hx⟩ else x₀

lemma sphereStateRecovery_measurable (x₀ : PhysicalSphere N) :
    Measurable (sphereStateRecovery x₀) := by
  classical
  apply Measurable.subtype_mk
  have he : (fun x => (sphereStateRecovery x₀ x).1) =
      {x : Vector N | OnSphere x}.piecewise id (fun _ => x₀.1) := by
    funext x
    by_cases hx : OnSphere x <;> simp [sphereStateRecovery,hx,Set.piecewise]
  change Measurable (fun x => (sphereStateRecovery x₀ x).1)
  rw [he]
  exact measurable_id.piecewise (sphere_measurableSet N) measurable_const

theorem sphereStateRecovery_coe (x₀ x : PhysicalSphere N) :
    sphereStateRecovery x₀ x.1 = x := by
  classical
  apply Subtype.ext
  simp [sphereStateRecovery,x.2]

/-- Sphere-supported ambient measures preserve the literal total variation
normalization under their faithful Borel inclusion. -/
theorem totalVariation_sphere_embedding (ν π : Measure (PhysicalSphere N))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure π] (x₀ : PhysicalSphere N) :
    totalVariation (ν.map Subtype.val) (π.map Subtype.val) = totalVariation ν π := by
  apply le_antisymm
  · exact totalVariation_map_le ν π measurable_subtype_coe
  · have h := totalVariation_map_le (ν.map Subtype.val) (π.map Subtype.val)
      (sphereStateRecovery_measurable x₀)
    have he : sphereStateRecovery x₀ ∘ (Subtype.val : PhysicalSphere N → Vector N) = id :=
      funext (sphereStateRecovery_coe x₀)
    rw [Measure.map_map (sphereStateRecovery_measurable x₀) measurable_subtype_coe,
      Measure.map_map (sphereStateRecovery_measurable x₀) measurable_subtype_coe,he,
      Measure.map_id,Measure.map_id] at h
    exact h

/-- The genuine source Gibbs probability kernel into S_N itself. -/
def sphereGibbsKernel (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) :
    Kernel (Field N μ) (PhysicalSphere N) :=
  (gibbsKernel μ β).map (sphereStateRecovery (sphereBasepoint hN))

instance sphereGibbsKernel_markov (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) :
    IsMarkovKernel (sphereGibbsKernel (N := N) hN μ β) :=
  Kernel.IsMarkovKernel.map _ (sphereStateRecovery_measurable _)

theorem sphereGibbsKernel_ambient_image (hN : 1 ≤ N) (μ : FiniteMixture)
    (β : ℝ) (H : Field N μ) :
    (sphereGibbsKernel hN μ β H).map Subtype.val = gibbsKernel μ β H := by
  rw [sphereGibbsKernel,Kernel.map_apply _ (sphereStateRecovery_measurable _),
    Measure.map_map measurable_subtype_coe (sphereStateRecovery_measurable _)]
  conv_rhs => rw [← Measure.map_id (μ := gibbsKernel μ β H)]
  apply Measure.map_congr
  rw [gibbsKernel_apply]
  filter_upwards [mixtureGibbsLaw_onSphere hN μ (coefficientLift μ H) β] with x hx
  classical
  simp [sphereStateRecovery,hx]

theorem sphereGibbsKernel_rotation (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (H : Field N μ) :
    (sphereGibbsKernel hN μ β H).map (sphereRotation U) =
      sphereGibbsKernel hN μ β (fieldRotation μ U H) := by
  have hEmb : MeasurableEmbedding (Subtype.val : PhysicalSphere N → Vector N) :=
    MeasurableEmbedding.subtype_coe (sphere_measurableSet N)
  apply hEmb.map_injective
  have hcoe : Measurable (Subtype.val : PhysicalSphere N → Vector N) := measurable_subtype_coe
  have hrot : Measurable (sphereRotation U) := (sphereRotation_continuous U).measurable
  rw [Measure.map_map hcoe hrot]
  have he : (Subtype.val : PhysicalSphere N → Vector N) ∘ sphereRotation U =
      U ∘ (Subtype.val : PhysicalSphere N → Vector N) := rfl
  rw [he,← Measure.map_map U.continuous.measurable measurable_subtype_coe,
    sphereGibbsKernel_ambient_image,sphereGibbsKernel_ambient_image]
  exact gibbsKernel_rotation hN μ β U H

/-- Actual conditional evolution commutes with the Borel sphere inclusion
for every arbitrary, possibly singular, field-dependent initial kernel. -/
theorem sphereEvolvedKernel_ambient_image (hN : 1 ≤ N) (μ : FiniteMixture)
    (β : ℝ) (t : ℝ≥0) (κ : Kernel (Field N μ) (PhysicalSphere N)) [IsMarkovKernel κ]
    (H : Field N μ) :
    (evolvedKernel κ (sphereTransitionKernel μ β t) H).map Subtype.val =
      evolvedKernel (κ.map Subtype.val) (transitionKernel μ β t) H := by
  let _ : IsMarkovKernel (κ.map (Subtype.val : PhysicalSphere N → Vector N)) :=
    Kernel.IsMarkovKernel.map _ measurable_subtype_coe
  ext B hB
  rw [Measure.map_apply measurable_subtype_coe hB,evolvedKernel_apply,
    Measure.bind_apply (measurable_subtype_coe hB) (conditionalKernel _ H).aemeasurable,
    evolvedKernel_apply,Kernel.map_apply _ measurable_subtype_coe,
    Measure.bind_apply hB (conditionalKernel _ H).aemeasurable,
    lintegral_map ((conditionalKernel (transitionKernel μ β t) H).measurable_coe hB)
      measurable_subtype_coe]
  apply lintegral_congr
  intro x
  have he := congrArg (fun M : Measure (Vector N) => M B)
    (sphereTransitionKernel_ambient_image hN μ β t H x)
  rw [Measure.map_apply measurable_subtype_coe hB] at he
  exact he

/-- The source distance uses intrinsic Borel events on S_N. -/
def sphereEndpointDistance (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (κ : Kernel (Field N μ) (PhysicalSphere N)) (H : Field N μ) : ℝ :=
  totalVariation (evolvedKernel κ (sphereTransitionKernel μ β t) H)
    (sphereGibbsKernel hN μ β H)

/-- Source lem:red-kernels(c), including every singular source initial law. -/
theorem sphereEndpointDistance_measurable (hN : 1 ≤ N) (μ : FiniteMixture)
    (β : ℝ) (t : ℝ≥0) (κ : Kernel (Field N μ) (PhysicalSphere N)) [IsMarkovKernel κ] :
    Measurable (sphereEndpointDistance hN μ β t κ) :=
  KernelTVMeasurable.measurable_kernel_totalVariation _ _

theorem sphereEndpointDistance_eq_ambient (hN : 1 ≤ N) (μ : FiniteMixture)
    (β : ℝ) (t : ℝ≥0) (κ : Kernel (Field N μ) (PhysicalSphere N)) [IsMarkovKernel κ]
    (H : Field N μ) :
    sphereEndpointDistance hN μ β t κ H = endpointDistance μ β t (κ.map Subtype.val) H := by
  let _ : IsMarkovKernel (κ.map (Subtype.val : PhysicalSphere N → Vector N)) :=
    Kernel.IsMarkovKernel.map _ measurable_subtype_coe
  unfold sphereEndpointDistance endpointDistance
  rw [← totalVariation_sphere_embedding _ _ (sphereBasepoint hN),
    sphereEvolvedKernel_ambient_image hN μ β t κ H,sphereGibbsKernel_ambient_image]

/-- The literal infimum over the entire real source time interval. -/
def sphereIntervalDistance (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (κ : Kernel (Field N μ) (PhysicalSphere N)) (H : Field N μ) : ℝ :=
  sInf ((fun t : ℝ => sphereEndpointDistance hN μ β t.toNNReal κ H) '' Icc 0 (T : ℝ))

/-- Genuine physical contraction and Gibbs stationarity identify the
all-time intrinsic sphere distance with its actual endpoint. -/
theorem sphereIntervalDistance_eq_endpoint (hN : 1 ≤ N) (μ : FiniteMixture)
    (β : ℝ) (T : ℝ≥0) (κ : Kernel (Field N μ) (PhysicalSphere N)) [IsMarkovKernel κ]
    (H : Field N μ) :
    sphereIntervalDistance hN μ β T κ H = sphereEndpointDistance hN μ β T κ H := by
  let _ : IsMarkovKernel (κ.map (Subtype.val : PhysicalSphere N → Vector N)) :=
    Kernel.IsMarkovKernel.map _ measurable_subtype_coe
  unfold sphereIntervalDistance
  simp_rw [sphereEndpointDistance_eq_ambient hN μ β _ κ H]
  rw [← intervalDistance_eq_endpoint hN μ β T (κ.map Subtype.val) H]
  unfold intervalDistance endpointDistance
  simp_rw [evolvedKernel_apply_physical]

theorem sphereIntervalDistance_measurable (hN : 1 ≤ N) (μ : FiniteMixture)
    (β : ℝ) (T : ℝ≥0) (κ : Kernel (Field N μ) (PhysicalSphere N)) [IsMarkovKernel κ] :
    Measurable (sphereIntervalDistance hN μ β T κ) := by
  have he : sphereIntervalDistance hN μ β T κ = sphereEndpointDistance hN μ β T κ :=
    funext (sphereIntervalDistance_eq_endpoint hN μ β T κ)
  rw [he]
  exact sphereEndpointDistance_measurable hN μ β T κ

end
end SlowEquilibration.SphericalFullFieldSphereTV
