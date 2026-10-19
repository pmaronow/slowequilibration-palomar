-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeFieldLaw
public import SlowEquilibration.CompactSphereCarrier
public import SlowEquilibration.SphericalSourceWeightedPartition

@[expose] public section

/-! # Actual source amplitude-one weighted-pressure law

The entire bank field law transports the literal weighted partition. This
provides the original tensor-model anchor for the finite amplitude pressure;
no limiting pressure premise enters the law identity.-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalBarycenter SphericalSourceWeightedPartition
open SphericalTaylorRemainder WholeFieldRegression SphericalGaussianJet
open scoped Topology ContDiff
set_option maxHeartbeats 1350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

/-- Deterministic planted drift and source penalty on the faithful compact
carrier, containing the full physical sphere. -/
def plantedPenaltyMap (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ) (x : Vector (n+1)) :
    C(CompactSphereCarrier.Carrier (n+1),ℝ) :=
  ⟨fun u => β^2*(n+1:ℝ)*μ.xi (overlap x u)-2*(n+1:ℝ)*sourceProfile J δ q₁ q₂ (overlap x u),by
    have hR : Continuous (fun u : CompactSphereCarrier.Carrier (n+1) => overlap x u) := by
      unfold overlap
      fun_prop
    have hxi : Continuous μ.xi := continuous_iff_continuousAt.mpr fun r => (μ.hasDerivAt_xi r).continuousAt
    exact (continuous_const.mul (hxi.comp hR)).sub
      (continuous_const.mul ((sourceProfile_contDiff J δ q₁ q₂).continuous.comp hR))⟩

/-- Literal Borel log partition functional of the entire continuous field. -/
def weightedLogPartitionFunctional (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ) (x : Vector (n+1))
    (f : C(CompactSphereCarrier.Carrier (n+1),ℝ)) : ℝ :=
  ContinuousFieldPartition.logPartition (CompactSphereCarrier.law (n+1)) 1
    (β • f+plantedPenaltyMap μ β J δ q₁ q₂ x)

theorem weightedLogPartitionFunctional_measurable (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) : Measurable (weightedLogPartitionFunctional μ β J δ q₁ q₂ x) := by
  let _ := CompactSphereCarrier.law_probability (by omega : 1≤n+1)
  have hLift : Continuous (fun f : C(CompactSphereCarrier.Carrier (n+1),ℝ) =>
      β • f+plantedPenaltyMap μ β J δ q₁ q₂ x) := by fun_prop
  exact (ContinuousFieldPartition.logPartition_measurable _ 1).comp hLift.measurable

/-- The compact functional evaluates to the literal source bank partition. -/
theorem weightedLogPartitionFunctional_bank (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (D : BankDisorder n μ) :
    weightedLogPartitionFunctional μ β J δ q₁ q₂ x
      (bankContinuousField μ x e p₀ s (Subtype.val : CompactSphereCarrier.Carrier (n+1) → Vector (n+1))
        continuous_subtype_val (euclideanBank D))=
      Real.log (amplitudePartition μ β J δ q₁ q₂ x e p₀ s D) := by
  unfold weightedLogPartitionFunctional ContinuousFieldPartition.logPartition ContinuousFieldPartition.partition
  congr 1
  simp only [ContinuousMap.add_apply,ContinuousMap.smul_apply,smul_eq_mul,one_mul,
    bankContinuousField_apply,unpackBank_euclideanBank,plantedPenaltyMap,ContinuousMap.coe_mk]
  have hf : Measurable (fun u : Vector (n+1) => Real.exp
      (β*amplitudePlantedField μ β x e p₀ s D u-2*(n+1:ℝ)*sourceProfile J δ q₁ q₂ (overlap x u))) := by
    apply Continuous.measurable
    have hR : Continuous (fun u : Vector (n+1) => overlap x u) := by unfold overlap; fun_prop
    exact Real.continuous_exp.comp (((amplitudePlantedField_contDiff μ β x e p₀ s D).continuous.const_mul β).sub (continuous_const.mul ((sourceProfile_contDiff J δ q₁ q₂).continuous.comp hR)))
  unfold amplitudePartition
  rw [← CompactSphereCarrier.integral_coe (by omega : 1≤n+1) _ hf]
  apply integral_congr_ae
  exact .of_forall fun u => by
    change Real.exp (β*amplitudeField μ x e p₀ s D u+(β^2*(n+1:ℝ)*μ.xi (overlap x u)-
      2*(n+1:ℝ)*sourceProfile J δ q₁ q₂ (overlap x u)))=
      Real.exp (β*amplitudePlantedField μ β x e p₀ s D u-
        2*(n+1:ℝ)*sourceProfile J δ q₁ q₂ (overlap x u))
    apply congrArg Real.exp
    unfold amplitudePlantedField
    ring

/-- The compact functional evaluates to the original actually planted
source weighted partition, with literal covariance translation. -/
theorem weightedLogPartitionFunctional_original (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (D : Disorder (n+1) μ.maxDegree) :
    weightedLogPartitionFunctional μ β J δ q₁ q₂ x
      (modelContinuousField (mixtureCoefficients μ)
        (Subtype.val : CompactSphereCarrier.Carrier (n+1) → Vector (n+1)) continuous_subtype_val
        (euclideanDisorder D))=
      Real.log (sourceWeightedPartition β
        (fieldOfMixture μ (D+plantedShift (mixtureCoefficients μ) β x)) J δ q₁ q₂ x) := by
  unfold weightedLogPartitionFunctional ContinuousFieldPartition.logPartition ContinuousFieldPartition.partition
  congr 1
  have hf : Measurable (fun u : Vector (n+1) => Real.exp
      (β*fieldOfMixture μ (D+plantedShift (mixtureCoefficients μ) β x) u-
        2*(n+1:ℝ)*sourceProfile J δ q₁ q₂ (overlap u x))) := by
    have hR : Continuous (fun u : Vector (n+1) => overlap u x) := by unfold overlap; fun_prop
    exact (Real.continuous_exp.comp (((fieldOfMixture_contDiff μ
      (D+plantedShift (mixtureCoefficients μ) β x)).continuous.const_mul β).sub
        (continuous_const.mul ((sourceProfile_contDiff J δ q₁ q₂).continuous.comp hR)))).measurable
  unfold sourceWeightedPartition
  simp only [Nat.cast_add,Nat.cast_one]
  rw [← CompactSphereCarrier.integral_coe (by omega : 1≤n+1) _ hf]
  apply integral_congr_ae
  exact .of_forall fun u => by
    simp only [ContinuousMap.add_apply,ContinuousMap.smul_apply,smul_eq_mul,one_mul,
      modelContinuousField_apply,valueObservation,flatJetCLM_apply,jet,iteratedFDeriv_zero_apply,
      unpack_euclideanDisorder,plantedPenaltyMap,fieldOfMixture,ContinuousMap.coe_mk]
    rw [field_add_plantedShift (by omega : 1≤n+1) (mixtureCoefficients μ)
      (mixtureCoefficients_nonnegative μ),covariancePolynomial_mixture]
    rw [show overlap (u:Vector (n+1)) x=overlap x u by unfold overlap; rw [real_inner_comm]]
    congr 1
    simp only [Nat.cast_add,Nat.cast_one]
    ring

/-- Literal equality of the actual bank and original planted weighted
log-partition laws, not just their expected limits. -/
theorem amplitudePartition_log_law_one (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (hx : ‖x‖^2=(n+1:ℝ)) (p₀ : Degree μ.maxDegree) :
    (bankLaw n μ).map (fun D => Real.log (amplitudePartition μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ (fun _ => 1) D))=
    (disorderLaw (n+1) μ.maxDegree).map (fun D => Real.log (sourceWeightedPartition β
      (fieldOfMixture μ (D+plantedShift (mixtureCoefficients μ) β x)) J δ q₁ q₂ x)) := by
  let X := fun D : BankDisorder n μ => bankContinuousField μ x (latitudeFrameAt x) p₀ (fun _ => 1)
    (Subtype.val : CompactSphereCarrier.Carrier (n+1) → Vector (n+1)) continuous_subtype_val (euclideanBank D)
  let Y := fun D : Disorder (n+1) μ.maxDegree => modelContinuousField (mixtureCoefficients μ)
    (Subtype.val : CompactSphereCarrier.Carrier (n+1) → Vector (n+1)) continuous_subtype_val (euclideanDisorder D)
  let f := weightedLogPartitionFunctional μ β J δ q₁ q₂ x
  have hX : Measurable X := (bankContinuousField μ x (latitudeFrameAt x) p₀ (fun _ => 1)
    (Subtype.val : CompactSphereCarrier.Carrier (n+1) → Vector (n+1)) continuous_subtype_val).continuous.measurable.comp (euclideanBank_measurable n μ)
  have hY : Measurable Y := (modelContinuousField (mixtureCoefficients μ)
    (Subtype.val : CompactSphereCarrier.Carrier (n+1) → Vector (n+1)) continuous_subtype_val).continuous.measurable.comp (euclideanDisorder_measurable _ _)
  have hLaw := congrArg (fun ν => ν.map f) (bankContinuousField_law_one μ x hx p₀
    (Subtype.val : CompactSphereCarrier.Carrier (n+1) → Vector (n+1)) continuous_subtype_val)
  rw [Measure.map_map (weightedLogPartitionFunctional_measurable μ β J δ q₁ q₂ x) hX,
    Measure.map_map (weightedLogPartitionFunctional_measurable μ β J δ q₁ q₂ x) hY] at hLaw
  have heX : f ∘ X=fun D => Real.log (amplitudePartition μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ (fun _ => 1) D) :=
    funext fun D => weightedLogPartitionFunctional_bank μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ (fun _ => 1) D
  have heY : f ∘ Y=fun D => Real.log (sourceWeightedPartition β
      (fieldOfMixture μ (D+plantedShift (mixtureCoefficients μ) β x)) J δ q₁ q₂ x) :=
    funext fun D => weightedLogPartitionFunctional_original μ β J δ q₁ q₂ x D
  change (bankLaw n μ).map (f ∘ X)=(disorderLaw (n+1) μ.maxDegree).map (f ∘ Y) at hLaw
  rw [heX,heY] at hLaw
  exact hLaw

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
