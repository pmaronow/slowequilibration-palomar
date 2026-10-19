-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceReductionConsumerAsymptotic
public import SlowEquilibration.ConditionedEntranceSourceFieldRotation
public import SlowEquilibration.SphericalFieldEntryMass
public import SlowEquilibration.SphericalFullFieldPathKernel

/-! The literal critical-center bands of manuscript `def:red-centers`, as
closed sets over the complete polynomial field. Their pullback, rotation
equivariance, uniform endpoint mass and Gibbs capture mass agree exactly
with the original tensor model, providing the geometric interface for
`thm:main-initial` (ii)/(iii) and `cor:cp-information`. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceInitialBandFieldAdapter

open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalDynamics SphericalGaussianJet SphericalMarkedWindows SphericalForm
open WholeFieldRegression SphericalRotationCovariance ConditionedEntrance
open SourceReductionClosedBandGraph SourceReductionConsumerBandBound
open SourceReductionConsumerAsymptotic SphericalFieldKernels
open SphericalFullFieldPathKernel SphericalAging.HardSphereDynamics
open scoped Topology NNReal RealInnerProductSpace

set_option autoImplicit false

variable {N : ℕ}

/-- The literal source band graph, evaluated through the continuous
coefficient section of the complete polynomial field. -/
def sourceBand (μ : FiniteMixture) (Q m M b : ℝ) (U : Set ℝ) :
    Set (SphericalFieldKernels.Field N μ × Vector N) :=
  (fun z => (SphericalFieldKernels.coefficientLift μ z.1, z.2)) ⁻¹'
    SourceReductionClosedBandGraph.physicalSphereBandUnionGraph μ Q m M b U

/-- Source `red-unions`: the band graph remains closed on actual fields. -/
theorem sourceBand_isClosed (μ : FiniteMixture) (Q m M b : ℝ)
    {U : Set ℝ} (hU : IsClosed U) :
    IsClosed (sourceBand (N := N) μ Q m M b U) := by
  exact (physicalSphereBandUnionGraph_isClosed μ Q m M b hU).preimage
    (((coefficientLift (N := N) μ).continuous.comp continuous_fst).prodMk continuous_snd)

/-- Complete polynomial equality preserves the center field and its
radial derivative, hence every clause of the literal source band. -/
private theorem physicalBand_mem_iff_of_field_eq (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (m M b : ℝ) (U : Set ℝ)
    (J K : Disorder N μ.maxDegree)
    (hfield : fieldOfMixture μ J = fieldOfMixture μ K) (x : Vector N) :
    (J,x) ∈ physicalSphereBandUnionGraph μ Q m M b U ↔
      (K,x) ∈ physicalSphereBandUnionGraph μ Q m M b U := by
  have hcenter : field (centerCoefficients (mixtureCoefficients μ) Q) J =
      field (centerCoefficients (mixtureCoefficients μ) Q) K := by
    funext u
    rw [field_center_scale _ (mixtureCoefficients_nonnegative μ) hQ,
      field_center_scale _ (mixtureCoefficients_nonnegative μ) hQ]
    exact congrFun hfield (Real.sqrt Q • u)
  have hradial (u : Vector N) :
      actualScore (centerCoefficients (mixtureCoefficients μ) Q) J u 1 =
        actualScore (centerCoefficients (mixtureCoefficients μ) Q) K u 1 := by
    simp only [actualScore, PiLp.smul_apply, scoreCLM_apply_one,
      unpack_euclideanDisorder, jet]
    rw [hcenter]
  unfold physicalSphereBandUnionGraph bandUnionGraph
    SourceReductionCompactBandProjection.bandUnionGraph windowCenterGraph
  simp only [mem_inter_iff, mem_ofPred_eq, hcenter, hradial]

/-- The source band loses no center, overlap or radial-mark information
when redundant tensor coefficients are removed. -/
theorem sourceBand_pullback (μ : FiniteMixture) {Q : ℝ} (hQ : 0 ≤ Q)
    (m M b : ℝ) (U : Set ℝ) (J : Disorder N μ.maxDegree) :
    SphericalFieldKernels.pullbackBand μ (sourceBand μ Q m M b U) J =
      SourceReductionConsumerBandBound.ambientWindowBandUnion μ Q m M b U J := by
  ext x
  exact physicalBand_mem_iff_of_field_eq μ hQ m M b U
    (coefficientLift μ (fieldMap μ J)) J (lifted_field_eq μ J) x

private theorem physicalBand_rotation_iff (μ : FiniteMixture)
    (Q m M b : ℝ) (Umark : Set ℝ) (V : Vector N ≃ₗᵢ[ℝ] Vector N)
    (J : Disorder N μ.maxDegree) (x : Vector N) :
    (rotatedDisorder V J,V x) ∈ physicalSphereBandUnionGraph μ Q m M b Umark ↔
      (J,x) ∈ physicalSphereBandUnionGraph μ Q m M b Umark := by
  have hcenter (u : Vector N) :
      (rotatedDisorder V J,V u) ∈ windowCenterGraph μ Q m M Umark ↔
        (J,u) ∈ windowCenterGraph μ Q m M Umark := by
    have hradial : actualScore (centerCoefficients (mixtureCoefficients μ) Q)
        (rotatedDisorder V J) (V u) 1 =
          actualScore (centerCoefficients (mixtureCoefficients μ) Q) J u 1 := by
      simp only [actualScore, PiLp.smul_apply, scoreCLM_apply_one,
        unpack_euclideanDisorder]
      rw [sourceCenterJet_rotated μ Q V J u]
    unfold windowCenterGraph
    simp only [mem_inter_iff, mem_ofPred_eq]
    rw [V.norm_map, sourceCenterGradient_rotated μ Q V J u,
      field_rotated, hradial]
    simp only [V.map_eq_zero_iff]
  have hband (u : Vector N) :
      (V x,V u) ∈ physicalBandRelation Q b ↔ (x,u) ∈ physicalBandRelation Q b := by
    unfold physicalBandRelation overlap
    change |inner ℝ (V x) (V u) / (N : ℝ) - Real.sqrt Q| ≤ b ↔
      |inner ℝ x u / (N : ℝ) - Real.sqrt Q| ≤ b
    rw [V.inner_map_map]
  change ((∃ u, (rotatedDisorder V J,u) ∈ windowCenterGraph μ Q m M Umark ∧
      (V x,u) ∈ physicalBandRelation Q b) ∧ ‖V x‖ ^ 2 = (N : ℝ)) ↔
    ((∃ u, (J,u) ∈ windowCenterGraph μ Q m M Umark ∧
      (x,u) ∈ physicalBandRelation Q b) ∧ ‖x‖ ^ 2 = (N : ℝ))
  rw [V.norm_map]
  apply and_congr_left
  intro _
  constructor
  · rintro ⟨u,hu,hb⟩
    refine ⟨V.symm u, (hcenter (V.symm u)).mp ?_, (hband (V.symm u)).mp ?_⟩
    · simpa only [V.apply_symm_apply] using hu
    · simpa only [V.apply_symm_apply] using hb
  · rintro ⟨u,hu,hb⟩
    exact ⟨V u, (hcenter u).mpr hu, (hband u).mpr hb⟩

/-- Source `red-unions`: rotation equivariance for the actual full-field
action, including all center and radial-mark conditions. -/
theorem sourceBand_rotation (μ : FiniteMixture) {Q : ℝ} (hQ : 0 ≤ Q)
    (m M b : ℝ) (Umark : Set ℝ) (V : Vector N ≃ₗᵢ[ℝ] Vector N)
    (H : SphericalFieldKernels.Field N μ) :
    Prod.mk (SphericalFullFieldPathKernel.fieldRotation μ V H) ⁻¹'
        sourceBand μ Q m M b Umark =
      V '' (Prod.mk H ⁻¹' sourceBand μ Q m M b Umark) := by
  have hsection : Prod.mk H ⁻¹' sourceBand μ Q m M b Umark =
      ambientWindowBandUnion μ Q m M b Umark (coefficientLift μ H) := by
    simpa only [pullbackBand, fieldMap_coefficientLift] using
      sourceBand_pullback μ hQ m M b Umark (coefficientLift μ H)
  change pullbackBand μ (sourceBand μ Q m M b Umark)
    (rotatedDisorder V (coefficientLift μ H)) = _
  rw [sourceBand_pullback μ hQ m M b Umark, hsection]
  ext x
  constructor
  · intro hx
    change (rotatedDisorder V (coefficientLift μ H),x) ∈
      physicalSphereBandUnionGraph μ Q m M b Umark at hx
    refine ⟨V.symm x, ?_, V.apply_symm_apply x⟩
    exact (physicalBand_rotation_iff μ Q m M b Umark V
      (coefficientLift μ H) (V.symm x)).mp
        (by simpa only [V.apply_symm_apply] using hx)
  · rintro ⟨y,hy,rfl⟩
    exact (physicalBand_rotation_iff μ Q m M b Umark V (coefficientLift μ H) y).mpr hy

/-- The source uniform endpoint entry mass is exactly the original
tensor-disorder expectation, with the literal critical-center band. -/
theorem sourceBand_uniformEntryMass_eq (hN : 1 ≤ N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (m M b β : ℝ) {U : Set ℝ} (hU : IsClosed U)
    (T : ℝ≥0) :
    SphericalFieldKernels.uniformEntryMass (N := N) μ β T (sourceBand μ Q m M b U) =
      ∫ J, (mixedTransitionKernel μ J β T ∘ₘ sphereLaw N).real
        (SourceReductionConsumerBandBound.ambientWindowBandUnion μ Q m M b U J)
        ∂disorderLaw N μ.maxDegree := by
  let _ := sphereLaw_probability N
  have hB := (sourceBand_isClosed (N := N) μ Q m M b hU).measurableSet
  rw [← uniform_conditional_mass_eq hN μ β T hB]
  have hm := ReductionJointInformation.conditionalMass_measurable
    (Kernel.const (SphericalFieldKernels.Field N μ) (sphereLaw N))
    (transitionKernel (N := N) μ β T) hB
  change (∫ H, ReductionJointInformation.conditionalMass
    (Kernel.const (SphericalFieldKernels.Field N μ) (sphereLaw N))
    (transitionKernel (N := N) μ β T) (sourceBand μ Q m M b U) H
    ∂(disorderLaw N μ.maxDegree).map (fieldMap (N := N) μ)) = _
  rw [integral_map (fieldMap (N := N) μ).measurable.aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  exact .of_forall fun J => by
    change (ReductionJointInformation.evolvedKernel
      (Kernel.const (SphericalFieldKernels.Field N μ) (sphereLaw N))
      (transitionKernel (N := N) μ β T) (fieldMap μ J)).real
        (pullbackBand μ (sourceBand μ Q m M b U) J) = _
    rw [evolvedKernel_fieldMap hN μ β T _ J]
    · simp only [sourceBand_pullback μ hQ m M b U J, Kernel.const_apply]
    · exact (sphereLaw_support hN).mono fun x hx => (onSphere_iff_norm_sq x).mpr hx

/-- Source `red-capture`: the expected missed Gibbs mass on actual
fields equals the original tensor-model capture quantity. -/
theorem sourceBand_capture_integral_eq (hN : 1 ≤ N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (m M b β : ℝ) {U : Set ℝ} (hU : IsClosed U) :
    (∫ H, (SphericalFieldKernels.gibbsKernel μ β H).real
      (Prod.mk H ⁻¹' sourceBand μ Q m M b U)ᶜ
      ∂SphericalFieldKernels.fieldLaw N μ) =
      ∫ J, SourceReductionConsumerAsymptotic.originalBandComplementMass μ Q m M b β U J
        ∂disorderLaw N μ.maxDegree := by
  have hm : Measurable (fun H : SphericalFieldKernels.Field N μ =>
      (gibbsKernel μ β H).real (Prod.mk H ⁻¹' sourceBand μ Q m M b U)ᶜ) := by
    have hmraw := (originalBandComplementMass_measurable hN μ Q m M b β hU).comp
      (coefficientLift (N := N) μ).measurable
    convert hmraw using 1
    funext H
    rw [gibbsKernel_apply]
    rfl
  change (∫ H, (gibbsKernel μ β H).real
    (Prod.mk H ⁻¹' sourceBand μ Q m M b U)ᶜ
    ∂(disorderLaw N μ.maxDegree).map (fieldMap (N := N) μ)) = _
  rw [integral_map (fieldMap (N := N) μ).measurable.aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  exact .of_forall fun J => by
    change (gibbsKernel μ β (fieldMap μ J)).real
      (Prod.mk (fieldMap μ J) ⁻¹' sourceBand μ Q m M b U)ᶜ = _
    rw [gibbsKernel_fieldMap]
    change (mixtureGibbsLaw μ β J).real (pullbackBand μ (sourceBand μ Q m M b U) J)ᶜ = _
    rw [sourceBand_pullback μ hQ m M b U J]
    rfl

end SlowEquilibration.SourceInitialBandFieldAdapter
