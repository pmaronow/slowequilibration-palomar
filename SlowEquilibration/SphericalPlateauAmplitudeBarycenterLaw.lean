-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudePressureLaw
public import SlowEquilibration.SphericalWeightedGibbsNormalization
public import SlowEquilibration.SphericalGibbsBochner
public import SlowEquilibration.SphericalWeightedReplicaTransfer

@[expose] public section

/-! # Literal whole-field transport of the actual source weighted barycenter

The weighted spin mean is a Borel functional of the whole continuous
Gaussian field. The amplitude-one bank therefore transports its entire
law to the original actually planted polynomial field.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalBarycenter SphericalTaylorRemainder
open WholeFieldRegression SphericalGaussianJet
open scoped Topology
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

/-- Genuine compact-field weighted mean of the physical normalized spin. -/
def weightedBarycenterFunctional (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ) (x : Vector (n+1))
    (f : C(CompactSphereCarrier.Carrier (n+1),ℝ)) : Vector (n+1) :=
  (∫ u : CompactSphereCarrier.Carrier (n+1),Real.exp
    (β*f u+plantedPenaltyMap μ β J δ q₁ q₂ x u) ∂CompactSphereCarrier.law (n+1))⁻¹ •
  (∫ u : CompactSphereCarrier.Carrier (n+1),Real.exp
    (β*f u+plantedPenaltyMap μ β J δ q₁ q₂ x u) • spin (u:Vector (n+1))
    ∂CompactSphereCarrier.law (n+1))

theorem weightedBarycenterFunctional_measurable (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) : Measurable (weightedBarycenterFunctional μ β J δ q₁ q₂ x) := by
  let _ := CompactSphereCarrier.law_probability (by omega : 1≤n+1)
  have hw : Continuous (fun z : C(CompactSphereCarrier.Carrier (n+1),ℝ) ×
      CompactSphereCarrier.Carrier (n+1) => Real.exp
      (β*z.1 z.2+plantedPenaltyMap μ β J δ q₁ q₂ x z.2)) := by fun_prop
  have hd := hw.stronglyMeasurable.integral_prod_right'
    (ν := CompactSphereCarrier.law (n+1))
  have hn : StronglyMeasurable (fun z : C(CompactSphereCarrier.Carrier (n+1),ℝ) ×
      CompactSphereCarrier.Carrier (n+1) => Real.exp
      (β*z.1 z.2+plantedPenaltyMap μ β J δ q₁ q₂ x z.2) • spin (z.2:Vector (n+1))) :=
    (hw.smul (spin_contDiff.continuous.comp continuous_snd.subtype_val)).stronglyMeasurable
  exact hd.measurable.inv.smul (hn.integral_prod_right'
    (ν := CompactSphereCarrier.law (n+1))).measurable

/-- Exact evaluation of the compact functional at any physical continuous
potential with the actual planted drift and source weight. -/
theorem weightedBarycenterFunctional_eq_barycenter (μ : FiniteMixture)
    (β J δ q₁ q₂ : ℝ) (x : Vector (n+1))
    (f : C(CompactSphereCarrier.Carrier (n+1),ℝ)) (H : Vector (n+1) → ℝ) (hH : Continuous H)
    (he : ∀ u : CompactSphereCarrier.Carrier (n+1),
      β*f u+plantedPenaltyMap μ β J δ q₁ q₂ x u=
        weightedPotential β H (sourceProfile J δ q₁ q₂) x u) :
    weightedBarycenterFunctional μ β J δ q₁ q₂ x f=
      barycenter β H (sourceProfile J δ q₁ q₂) x := by
  let V := weightedPotential β H (sourceProfile J δ q₁ q₂) x
  have hV : Continuous V := weightedPotential_continuous β hH
    (sourceProfile_contDiff J δ q₁ q₂).continuous x
  have hden : (∫ u : CompactSphereCarrier.Carrier (n+1),Real.exp
      (β*f u+plantedPenaltyMap μ β J δ q₁ q₂ x u) ∂CompactSphereCarrier.law (n+1))=
      partition (n+1) 1 V := by
    simp_rw [he]
    change (∫ u : CompactSphereCarrier.Carrier (n+1),Real.exp (V u)
      ∂CompactSphereCarrier.law (n+1))=partition (n+1) 1 V
    have hi := CompactSphereCarrier.integral_coe (by omega : 1≤n+1)
      (fun u => Real.exp (V u)) (Real.continuous_exp.comp hV).measurable
    simpa only [partition,one_mul] using hi
  have hnum : (∫ u : CompactSphereCarrier.Carrier (n+1),Real.exp
      (β*f u+plantedPenaltyMap μ β J δ q₁ q₂ x u) • spin (u:Vector (n+1))
      ∂CompactSphereCarrier.law (n+1))=
      ∫ u : Vector (n+1),Real.exp (V u) • spin u ∂sphereLaw (n+1) := by
    simp_rw [he]
    have hm := integral_map measurable_subtype_coe.aemeasurable
      (((Real.continuous_exp.comp hV).smul spin_contDiff.continuous).aestronglyMeasurable
        (μ := (CompactSphereCarrier.law (n+1)).map Subtype.val))
    rw [CompactSphereCarrier.law_map_coe (by omega : 1≤n+1)] at hm
    exact hm.symm
  rw [weightedBarycenterFunctional,hden,hnum,barycenter_eq_integral
    (by omega : 1≤n+1) β hH (sourceProfile_contDiff J δ q₁ q₂),
    weightedLaw_eq_gibbsLaw (by omega : 1≤n+1) β hH (sourceProfile_contDiff J δ q₁ q₂),
    integral_gibbsLaw_bochner (by omega : 1≤n+1) 1 hV]
  simp only [one_mul]

/-- Exact evaluation at the literal amplitude bank polynomial. -/
theorem weightedBarycenterFunctional_bank (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (D : BankDisorder n μ) :
    weightedBarycenterFunctional μ β J δ q₁ q₂ x
      (bankContinuousField μ x e p₀ s (Subtype.val : CompactSphereCarrier.Carrier (n+1) → Vector (n+1))
        continuous_subtype_val (euclideanBank D))=
      barycenter β (amplitudePlantedField μ β x e p₀ s D) (sourceProfile J δ q₁ q₂) x := by
  apply weightedBarycenterFunctional_eq_barycenter μ β J δ q₁ q₂ x _ _
    (amplitudePlantedField_contDiff μ β x e p₀ s D).continuous
  intro u
  simp only [bankContinuousField_apply,unpackBank_euclideanBank,plantedPenaltyMap,
    ContinuousMap.coe_mk,weightedPotential,amplitudePlantedField]
  simp only [Nat.cast_add,Nat.cast_one]
  ring

/-- Exact evaluation at the original full polynomial after true planting. -/
theorem weightedBarycenterFunctional_original (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (D : Disorder (n+1) μ.maxDegree) :
    weightedBarycenterFunctional μ β J δ q₁ q₂ x
      (modelContinuousField (mixtureCoefficients μ)
        (Subtype.val : CompactSphereCarrier.Carrier (n+1) → Vector (n+1)) continuous_subtype_val
        (euclideanDisorder D))=
      sourceObservable β (fieldOfMixture μ (D+plantedShift (mixtureCoefficients μ) β x))
        J δ q₁ q₂ x := by
  apply weightedBarycenterFunctional_eq_barycenter μ β J δ q₁ q₂ x _ _
    (fieldOfMixture_contDiff μ (D+plantedShift (mixtureCoefficients μ) β x)).continuous
  intro u
  simp only [modelContinuousField_apply,valueObservation,flatJetCLM_apply,jet,
    iteratedFDeriv_zero_apply,unpack_euclideanDisorder,plantedPenaltyMap,fieldOfMixture,
    ContinuousMap.coe_mk,weightedPotential]
  rw [field_add_plantedShift (by omega : 1≤n+1) (mixtureCoefficients μ)
    (mixtureCoefficients_nonnegative μ),covariancePolynomial_mixture]
  rw [show overlap (u:Vector (n+1)) x=overlap x u by unfold overlap;rw [real_inner_comm]]
  simp only [Nat.cast_add,Nat.cast_one]
  ring

/-- The entire actual weighted spin-mean law at amplitude one equals the
original actually planted source-observable law. -/
theorem amplitudeBarycenter_law_one (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (hx : ‖x‖^2=(n+1:ℝ)) (p₀ : Degree μ.maxDegree) :
    (bankLaw n μ).map (fun D => barycenter β
      (amplitudePlantedField μ β x (latitudeFrameAt x) p₀ (fun _ => 1) D)
      (sourceProfile J δ q₁ q₂) x)=
    (disorderLaw (n+1) μ.maxDegree).map (fun D => sourceObservable β
      (fieldOfMixture μ (D+plantedShift (mixtureCoefficients μ) β x)) J δ q₁ q₂ x) := by
  let X := fun D : BankDisorder n μ => bankContinuousField μ x (latitudeFrameAt x) p₀ (fun _ => 1)
    (Subtype.val : CompactSphereCarrier.Carrier (n+1) → Vector (n+1)) continuous_subtype_val (euclideanBank D)
  let Y := fun D : Disorder (n+1) μ.maxDegree => modelContinuousField (mixtureCoefficients μ)
    (Subtype.val : CompactSphereCarrier.Carrier (n+1) → Vector (n+1)) continuous_subtype_val (euclideanDisorder D)
  let f := weightedBarycenterFunctional μ β J δ q₁ q₂ x
  have hX : Measurable X := (bankContinuousField μ x (latitudeFrameAt x) p₀ (fun _ => 1)
    (Subtype.val : CompactSphereCarrier.Carrier (n+1) → Vector (n+1)) continuous_subtype_val).continuous.measurable.comp (euclideanBank_measurable n μ)
  have hY : Measurable Y := (modelContinuousField (mixtureCoefficients μ)
    (Subtype.val : CompactSphereCarrier.Carrier (n+1) → Vector (n+1)) continuous_subtype_val).continuous.measurable.comp (euclideanDisorder_measurable _ _)
  have hLaw := congrArg (fun ν => ν.map f) (bankContinuousField_law_one μ x hx p₀
    (Subtype.val : CompactSphereCarrier.Carrier (n+1) → Vector (n+1)) continuous_subtype_val)
  rw [Measure.map_map (weightedBarycenterFunctional_measurable μ β J δ q₁ q₂ x) hX,
    Measure.map_map (weightedBarycenterFunctional_measurable μ β J δ q₁ q₂ x) hY] at hLaw
  have heX : f ∘ X=fun D => barycenter β
      (amplitudePlantedField μ β x (latitudeFrameAt x) p₀ (fun _ => 1) D)
      (sourceProfile J δ q₁ q₂) x :=
    funext fun D => weightedBarycenterFunctional_bank μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ (fun _ => 1) D
  have heY : f ∘ Y=fun D => sourceObservable β
      (fieldOfMixture μ (D+plantedShift (mixtureCoefficients μ) β x)) J δ q₁ q₂ x :=
    funext fun D => weightedBarycenterFunctional_original μ β J δ q₁ q₂ x D
  change (bankLaw n μ).map (f ∘ X)=(disorderLaw (n+1) μ.maxDegree).map (f ∘ Y) at hLaw
  rw [heX,heY] at hLaw
  exact hLaw

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
