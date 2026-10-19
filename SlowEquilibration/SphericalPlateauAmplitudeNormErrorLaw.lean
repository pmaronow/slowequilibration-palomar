-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeBarycenterLaw
public import SlowEquilibration.SphericalPlantedShiftRegularity

@[expose] public section

/-! # Exact actual planted norm-error transfer from the amplitude bank

Whole-field transport and the literal covariance planting identify every
fixed-reference error expectation. A uniform bank estimate then supplies
the actual joint planted source error, with no reference-frame measurability
assumption or contiguity premise.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalBarycenter SphericalWeightedReplicaPlateau
open scoped Topology
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

/-- Literal physical squared norm error of the actual amplitude mean. -/
def amplitudeNormError (μ : FiniteMixture) (β J δ q₁ q₂ q : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (D : BankDisorder n μ) : ℝ :=
  (‖barycenter β (amplitudePlantedField μ β x e p₀ s D) (sourceProfile J δ q₁ q₂) x‖^2-q)^2

theorem amplitudeBarycenter_measurable (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) :
    Measurable (fun D : BankDisorder n μ =>
      barycenter β (amplitudePlantedField μ β x e p₀ s D) (sourceProfile J δ q₁ q₂) x) := by
  have h := (weightedBarycenterFunctional_measurable μ β J δ q₁ q₂ x).comp
    ((bankContinuousField μ x e p₀ s
      (Subtype.val : CompactSphereCarrier.Carrier (n+1) → Vector (n+1)) continuous_subtype_val).continuous.measurable.comp
      (euclideanBank_measurable n μ))
  change Measurable (fun D : BankDisorder n μ => weightedBarycenterFunctional μ β J δ q₁ q₂ x
    (bankContinuousField μ x e p₀ s
      (Subtype.val : CompactSphereCarrier.Carrier (n+1) → Vector (n+1)) continuous_subtype_val (euclideanBank D))) at h
  simpa only [weightedBarycenterFunctional_bank] using h

theorem amplitudeNormError_measurable (μ : FiniteMixture) (β J δ q₁ q₂ q : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) :
    Measurable (amplitudeNormError μ β J δ q₁ q₂ q x e p₀ s) :=
  (((amplitudeBarycenter_measurable μ β J δ q₁ q₂ x e p₀ s).norm.pow_const 2).sub_const q).pow_const 2

/-- Exact literal norm-error expectation, not an asymptotic-law premise. -/
theorem amplitudeNormError_expectation_one (μ : FiniteMixture) (β J δ q₁ q₂ q : ℝ)
    (x : Vector (n+1)) (hx : ‖x‖^2=(n+1:ℝ)) (p₀ : Degree μ.maxDegree) :
    (∫ D,amplitudeNormError μ β J δ q₁ q₂ q x (latitudeFrameAt x) p₀ (fun _ => 1) D
      ∂bankLaw n μ)=
      ∫ D : Disorder (n+1) μ.maxDegree,
        sourceNormError μ β J δ q₁ q₂ q (D+plantedShift (mixtureCoefficients μ) β x,x)
        ∂disorderLaw (n+1) μ.maxDegree := by
  let F := fun v : Vector (n+1) => (‖v‖^2-q)^2
  have hF : Continuous F := by fun_prop
  have hBank := amplitudeBarycenter_measurable μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ (fun _ => 1)
  have hOriginal := (weightedBarycenterFunctional_measurable μ β J δ q₁ q₂ x).comp
    ((SphericalTaylorRemainder.modelContinuousField (mixtureCoefficients μ)
      (Subtype.val : CompactSphereCarrier.Carrier (n+1) → Vector (n+1)) continuous_subtype_val).continuous.measurable.comp
      (SphericalTaylorRemainder.euclideanDisorder_measurable (n+1) μ.maxDegree))
  change Measurable (fun D : Disorder (n+1) μ.maxDegree => weightedBarycenterFunctional μ β J δ q₁ q₂ x
    (SphericalTaylorRemainder.modelContinuousField (mixtureCoefficients μ)
      (Subtype.val : CompactSphereCarrier.Carrier (n+1) → Vector (n+1)) continuous_subtype_val
      (SphericalModel.euclideanDisorder D))) at hOriginal
  simp only [weightedBarycenterFunctional_original] at hOriginal
  have hL : (∫ v,F v ∂(bankLaw n μ).map (fun D => barycenter β
      (amplitudePlantedField μ β x (latitudeFrameAt x) p₀ (fun _ => 1) D)
        (sourceProfile J δ q₁ q₂) x))=
      ∫ D,F (barycenter β (amplitudePlantedField μ β x (latitudeFrameAt x) p₀ (fun _ => 1) D)
        (sourceProfile J δ q₁ q₂) x) ∂bankLaw n μ :=
    integral_map hBank.aemeasurable hF.aestronglyMeasurable
  have hR : (∫ v,F v ∂(disorderLaw (n+1) μ.maxDegree).map (fun D => sourceObservable β
      (fieldOfMixture μ (D+plantedShift (mixtureCoefficients μ) β x)) J δ q₁ q₂ x))=
      ∫ D,F (sourceObservable β (fieldOfMixture μ (D+plantedShift (mixtureCoefficients μ) β x))
        J δ q₁ q₂ x) ∂disorderLaw (n+1) μ.maxDegree :=
    integral_map hOriginal.aemeasurable hF.aestronglyMeasurable
  rw [amplitudeBarycenter_law_one μ β J δ q₁ q₂ x hx p₀] at hL
  change (∫ D,F (barycenter β (amplitudePlantedField μ β x (latitudeFrameAt x) p₀ (fun _ => 1) D)
    (sourceProfile J δ q₁ q₂) x) ∂bankLaw n μ)=
    ∫ D,F (sourceObservable β (fieldOfMixture μ (D+plantedShift (mixtureCoefficients μ) β x))
      J δ q₁ q₂ x) ∂disorderLaw (n+1) μ.maxDegree
  exact hL.symm.trans hR

/-- Uniform actual bank norm errors imply the exact joint planted error
limit. The original reference integral and covariance shift are proved. -/
theorem sourceNormError_planted_tendsto_of_uniform_bank (μ : FiniteMixture)
    (β J δ q₁ q₂ : ℝ) {q : ℝ} (hq : q∈Icc (0:ℝ) 1) (p₀ : Degree μ.maxDegree)
    (hBank : ∀ ε : ℝ,0<ε → ∀ᶠ n : ℕ in atTop,∀ x : Vector (n+1),
      ‖x‖^2=(n+1:ℝ) →
      (∫ D,amplitudeNormError μ β J δ q₁ q₂ q x (latitudeFrameAt x) p₀ (fun _ => 1) D
        ∂bankLaw n μ)≤ε) :
    Tendsto (fun N => ∫ z : Disorder N μ.maxDegree × Vector N,
      sourceNormError μ β J δ q₁ q₂ q z ∂plantedLaw (mixtureCoefficients μ) β)
      atTop (𝓝 (0:ℝ)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hBank (ε/2) (half_pos hε)] with n hBankN
  let F := sourceNormError (N := n+1) μ β J δ q₁ q₂ q
  let G := fun x : Vector (n+1) => ∫ D : Disorder (n+1) μ.maxDegree,
    F (D+plantedShift (mixtureCoefficients μ) β x,x) ∂disorderLaw (n+1) μ.maxDegree
  have hF : Measurable F := sourceNormError_measurable μ β J δ q₁ q₂ q
  have hBound (z : Disorder (n+1) μ.maxDegree × Vector (n+1)) : |F z|≤1 := by
    rw [abs_of_nonneg (sourceNormError_nonnegative μ β J δ q₁ q₂ q z)]
    exact sourceNormError_le_one (by omega) μ β J δ q₁ q₂ hq z
  have hFG : Measurable (fun z : Vector (n+1) × Disorder (n+1) μ.maxDegree =>
      F (z.2+plantedShift (mixtureCoefficients μ) β z.1,z.1)) :=
    hF.comp ((measurable_snd.add ((plantedShift_measurable _ _).comp measurable_fst)).prodMk measurable_fst)
  have hG : StronglyMeasurable G := hFG.stronglyMeasurable.integral_prod_right'
    (ν := disorderLaw (n+1) μ.maxDegree)
  have hGBound (x : Vector (n+1)) : |G x|≤1 := by
    rw [← Real.norm_eq_abs]
    change ‖∫ D : Disorder (n+1) μ.maxDegree,F (D+plantedShift (mixtureCoefficients μ) β x,x)
      ∂disorderLaw (n+1) μ.maxDegree‖≤1
    apply (norm_integral_le_integral_norm _).trans
    change (∫ D : Disorder (n+1) μ.maxDegree,
      ‖F (D+plantedShift (mixtureCoefficients μ) β x,x)‖ ∂disorderLaw (n+1) μ.maxDegree)≤1
    have hi : Integrable (fun D : Disorder (n+1) μ.maxDegree =>
        F (D+plantedShift (mixtureCoefficients μ) β x,x)) (disorderLaw (n+1) μ.maxDegree) :=
      Integrable.of_bound (hF.comp ((measurable_id.add measurable_const).prodMk measurable_const)).aestronglyMeasurable 1
        (.of_forall fun D => by simpa only [Real.norm_eq_abs] using hBound (D+plantedShift (mixtureCoefficients μ) β x,x))
    have hh := integral_mono hi.norm (integrable_const (1:ℝ))
      (fun D => by simpa only [Real.norm_eq_abs] using hBound (D+plantedShift (mixtureCoefficients μ) β x,x))
    simpa only [integral_const,probReal_univ,smul_eq_mul,mul_one,one_mul] using hh
  have hiG : Integrable G (sphereLaw (n+1)) :=
    Integrable.of_bound hG.aestronglyMeasurable 1 (.of_forall fun x => by simpa only [Real.norm_eq_abs] using hGBound x)
  have hupper : (∫ x,G x ∂sphereLaw (n+1))≤ε/2 := by
    have hh := integral_mono_ae hiG (integrable_const (ε/2)) (by
      filter_upwards [sphereLaw_support (by omega : 1≤n+1)] with x hx
      change (∫ D : Disorder (n+1) μ.maxDegree,sourceNormError μ β J δ q₁ q₂ q
        (D+plantedShift (mixtureCoefficients μ) β x,x) ∂disorderLaw (n+1) μ.maxDegree)≤ε/2
      rw [← amplitudeNormError_expectation_one μ β J δ q₁ q₂ q x
        (by simpa only [Nat.cast_add,Nat.cast_one] using hx) p₀]
      exact hBankN x (by simpa only [Nat.cast_add,Nat.cast_one] using hx))
    simpa only [integral_const,probReal_univ,smul_eq_mul,mul_one,one_mul] using hh
  have hShift := planted_joint_expectation_eq_shift (by omega : 1≤n+1)
    (mixtureCoefficients μ) (mixtureCoefficients_nonnegative μ) β F hF 1 hBound
  change (∫ z,F z ∂plantedLaw (mixtureCoefficients μ) β)=∫ x,G x ∂sphereLaw (n+1) at hShift
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg (sourceNormError_nonnegative μ β J δ q₁ q₂ q)),hShift]
  exact hupper.trans_lt (by linarith)

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
