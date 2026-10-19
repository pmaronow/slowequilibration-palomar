-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalWeightedReplicaPlateau
public import SlowEquilibration.SphericalGibbsAllDimensions
public import Mathlib.Probability.Kernel.MeasurableIntegral

@[expose] public section

/-! # Borel observables for the actual stronger plateau argument

The overlap-weighted Gibbs barycenter is jointly Borel in the literal
Gaussian tensors and reference point. Its actual replica moment and norm
fluctuation therefore define Borel disorder events.
-/
namespace SlowEquilibration.SphericalWeightedReplicaPlateau
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalBarycenter
open scoped Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

/-- Joint Borel dependence of the literal normalized Gibbs barycenter,
including every exceptional reference point. -/
theorem sourceObservable_joint_measurable (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ) :
    Measurable (fun z : Disorder N μ.maxDegree × Vector N =>
      sourceObservable β (fieldOfMixture μ z.1) J δ q₁ q₂ z.2) := by
  let κ : Kernel (Disorder N μ.maxDegree × Vector N) (Vector N) := (allDimensionGibbsKernel (N := N) (mixtureCoefficients μ) β).comap
    (Prod.fst : Disorder N μ.maxDegree × Vector N → Disorder N μ.maxDegree) measurable_fst
  have hd : Measurable (fun z : Disorder N μ.maxDegree × Vector N =>
      denominator β (fieldOfMixture μ z.1) (sourceProfile J δ q₁ q₂) z.2) := by
    have hf : StronglyMeasurable (fun z : (Disorder N μ.maxDegree × Vector N) × Vector N =>
        (psi (sourceProfile J δ q₁ q₂) z.1.2 z.2)^2) :=
      (((psi_joint_contDiff (sourceProfile_contDiff J δ q₁ q₂)).continuous.comp
        (continuous_snd.prodMk continuous_fst.snd)).pow 2).stronglyMeasurable
    change Measurable (fun z : Disorder N μ.maxDegree × Vector N =>
      ∫ u, (psi (sourceProfile J δ q₁ q₂) z.2 u)^2 ∂gibbsLaw N β (field (mixtureCoefficients μ) z.1))
    simpa only [κ,Kernel.comap_apply,allDimensionGibbsKernel_apply] using (hf.integral_kernel_prod_right' (κ := κ)).measurable
  have hn : Measurable (fun z : Disorder N μ.maxDegree × Vector N =>
      numerator β (fieldOfMixture μ z.1) (sourceProfile J δ q₁ q₂) z.2) := by
    have hf : StronglyMeasurable (fun z : (Disorder N μ.maxDegree × Vector N) × Vector N =>
        (psi (sourceProfile J δ q₁ q₂) z.1.2 z.2)^2 • spin z.2) :=
      ((numerator_joint_contDiff (sourceProfile_contDiff J δ q₁ q₂)).continuous.comp
        (continuous_snd.prodMk continuous_fst.snd)).stronglyMeasurable
    change Measurable (fun z : Disorder N μ.maxDegree × Vector N =>
      ∫ u, (psi (sourceProfile J δ q₁ q₂) z.2 u)^2 • spin u ∂gibbsLaw N β (field (mixtureCoefficients μ) z.1))
    simpa only [κ,Kernel.comap_apply,allDimensionGibbsKernel_apply] using (hf.integral_kernel_prod_right' (κ := κ)).measurable
  exact hd.inv.smul hn

/-- The literal source weighted-replica moment is Borel in the disorder. -/
theorem sourceWeightedReplicaMoment_measurable (hN : 1 ≤ N) (μ : FiniteMixture)
    (β J δ q₁ q₂ : ℝ) :
    Measurable (fun D : Disorder N μ.maxDegree =>
      sourceWeightedReplicaMoment μ β D J δ q₁ q₂) := by
  have h := ((sourceObservable_joint_measurable (N := N) μ β J δ q₁ q₂).norm.pow_const 2).stronglyMeasurable.integral_kernel_prod_right'
      (κ := allDimensionGibbsKernel (mixtureCoefficients μ) β)
  have he : (fun D : Disorder N μ.maxDegree => sourceWeightedReplicaMoment μ β D J δ q₁ q₂) =
      (fun D => ∫ x, ‖sourceObservable β (fieldOfMixture μ D) J δ q₁ q₂ x‖^2
        ∂allDimensionGibbsKernel (mixtureCoefficients μ) β D) := by
    funext D
    rw [sourceWeightedReplicaMoment_eq_norm hN,allDimensionGibbsKernel_apply]
    rfl
  rw [he]
  exact h.measurable

/-- The actual Gibbs-reference fluctuation appearing in source prop:pl-norm. -/
def sourceNormFluctuation (μ : FiniteMixture) (β J δ q₁ q₂ q : ℝ)
    (D : Disorder N μ.maxDegree) : ℝ :=
  ∫ x, (‖sourceObservable β (fieldOfMixture μ D) J δ q₁ q₂ x‖^2-q)^2
    ∂mixtureGibbsLaw μ β D

theorem sourceNormFluctuation_measurable (μ : FiniteMixture) (β J δ q₁ q₂ q : ℝ) :
    Measurable (sourceNormFluctuation (N := N) μ β J δ q₁ q₂ q) := by
  have h := (((sourceObservable_joint_measurable (N := N) μ β J δ q₁ q₂).norm.pow_const 2).sub_const q).pow_const 2
  have hm := h.stronglyMeasurable.integral_kernel_prod_right'
    (κ := allDimensionGibbsKernel (mixtureCoefficients μ) β)
  change Measurable (fun D : Disorder N μ.maxDegree =>
    ∫ x, (‖sourceObservable β (fieldOfMixture μ D) J δ q₁ q₂ x‖^2-q)^2
      ∂gibbsLaw N β (field (mixtureCoefficients μ) D))
  simpa only [allDimensionGibbsKernel_apply] using hm.measurable

theorem sourceWeightedReplicaMoment_event_measurable (hN : 1 ≤ N) (μ : FiniteMixture)
    (β J δ q₁ q₂ m : ℝ) :
    MeasurableSet {D : Disorder N μ.maxDegree | sourceWeightedReplicaMoment μ β D J δ q₁ q₂ ≤ m} :=
  measurableSet_le (sourceWeightedReplicaMoment_measurable hN μ β J δ q₁ q₂) measurable_const

/-- The integrated source fluctuation controls deviation of the genuine
weighted-replica moment, by the probability-space square-integral bound. -/
theorem sourceWeightedReplicaMoment_deviation_sq_le (hN : 1 ≤ N) (μ : FiniteMixture)
    (β J δ q₁ q₂ q : ℝ) (D : Disorder N μ.maxDegree) :
    (sourceWeightedReplicaMoment μ β D J δ q₁ q₂-q)^2 ≤
      sourceNormFluctuation μ β J δ q₁ q₂ q D := by
  let f := fun x : Vector N => ‖sourceObservable β (fieldOfMixture μ D) J δ q₁ q₂ x‖^2-q
  have hf : Continuous f := ((sourceObservable_contDiff hN β
    (fieldOfMixture_contDiff μ D).continuous J δ q₁ q₂).continuous.norm.pow 2).sub continuous_const
  let _ := gibbsLaw_probability hN β (fieldOfMixture_contDiff μ D).continuous
  let _ : IsProbabilityMeasure (mixtureGibbsLaw μ β D) := by
    change IsProbabilityMeasure (gibbsLaw N β (fieldOfMixture μ D))
    exact gibbsLaw_probability hN β (fieldOfMixture_contDiff μ D).continuous
  have hi : Integrable (fun x => f x^2) (mixtureGibbsLaw μ β D) :=
    SphericalForm.integrable_gibbs_of_continuous hN β (fieldOfMixture_contDiff μ D).continuous (hf.pow 2)
  have hm : MemLp f 2 (mixtureGibbsLaw μ β D) :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr hi
  have hBound := SphericalAging.PredictableDriftTime.integral_sq_le_measure_mul_integral_sq
    (mixtureGibbsLaw μ β D) f hm
  have he : (∫ x, f x ∂mixtureGibbsLaw μ β D)=sourceWeightedReplicaMoment μ β D J δ q₁ q₂-q := by
    rw [sourceWeightedReplicaMoment_eq_norm hN]
    change (∫ x, (‖sourceObservable β (fieldOfMixture μ D) J δ q₁ q₂ x‖^2-q)
      ∂mixtureGibbsLaw μ β D)=_
    have hnorm : Integrable (fun x => ‖sourceObservable β (fieldOfMixture μ D) J δ q₁ q₂ x‖^2)
        (mixtureGibbsLaw μ β D) :=
      SphericalForm.integrable_gibbs_of_continuous hN β (fieldOfMixture_contDiff μ D).continuous
        ((sourceObservable_contDiff hN β (fieldOfMixture_contDiff μ D).continuous
          J δ q₁ q₂).continuous.norm.pow 2)
    rw [integral_sub hnorm (integrable_const q)]
    simp only [integral_const,probReal_univ,one_smul]
  rw [he] at hBound
  change (sourceWeightedReplicaMoment μ β D J δ q₁ q₂-q)^2 ≤
    ∫ x, f x^2 ∂mixtureGibbsLaw μ β D
  simpa only [probReal_univ,one_mul] using hBound

end
end SlowEquilibration.SphericalWeightedReplicaPlateau
