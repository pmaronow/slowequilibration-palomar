-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeAnnealed
public import SlowEquilibration.SphericalUniformPoleMass
public import SlowEquilibration.GaussianSpinKernels
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

@[expose] public section

/-! # Actual restricted amplitude partition annealed budget and Markov bound -/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalBarycenter
open scoped Topology ENNReal
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

/-- Literal restricted sphere partition of the actual weighted bank. -/
def amplitudeRestrictedPartition (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (E : Set (Vector (n+1))) (D : BankDisorder n μ) : ℝ :=
  ∫ u in E,Real.exp (β*amplitudePlantedField μ β x (latitudeFrameAt x) p₀ s D u-
    2*((n+1:ℕ):ℝ)*sourceProfile J δ q₁ q₂ (overlap x u)) ∂sphereLaw (n+1)

private theorem weightedPoint_measurable (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) :
    Measurable (fun z : BankDisorder n μ × Vector (n+1) =>
      Real.exp (β*amplitudePlantedField μ β x (latitudeFrameAt x) p₀ s z.1 z.2-
        2*((n+1:ℕ):ℝ)*sourceProfile J δ q₁ q₂ (overlap x z.2))) := by
  let A := amplitudeBasePotential μ β J δ q₁ q₂ x
  let L := amplitudeBankLinear μ β x (latitudeFrameAt x) p₀ s
  have hEval := (GaussianSpinInterpolation.measurable_feature_evaluation L
    (amplitudeBankLinear_continuous μ β x (latitudeFrameAt x) p₀ s).measurable).comp
      (((euclideanBank_measurable n μ).comp measurable_fst).prodMk measurable_snd)
  have hA : Measurable (fun z : BankDisorder n μ × Vector (n+1) => A z.2) :=
    (amplitudeBasePotential_continuous μ β J δ q₁ q₂ x).measurable.comp measurable_snd
  have h := (hA.add hEval).exp
  have he : (fun z : BankDisorder n μ × Vector (n+1) => Real.exp (A z.2+L z.2 (euclideanBank z.1)))=
      fun z => Real.exp (β*amplitudePlantedField μ β x (latitudeFrameAt x) p₀ s z.1 z.2-
        2*((n+1:ℕ):ℝ)*sourceProfile J δ q₁ q₂ (overlap x z.2)) := by
    funext z
    rw [amplitudeBankLinear_apply,unpackBank_euclideanBank]
    congr 1
    unfold A amplitudeBasePotential amplitudePlantedField
    simp only [Nat.cast_add,Nat.cast_one]
    ring
  change Measurable (fun z : BankDisorder n μ × Vector (n+1) => Real.exp (A z.2+L z.2 (euclideanBank z.1))) at h
  rwa [he] at h

private theorem weightedPoint_bank_integrable (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (u : Vector (n+1)) :
    Integrable (fun D : BankDisorder n μ =>
      Real.exp (β*amplitudePlantedField μ β x (latitudeFrameAt x) p₀ s D u-
        2*((n+1:ℕ):ℝ)*sourceProfile J δ q₁ q₂ (overlap x u))) (bankLaw n μ) := by
  let v := amplitudeBankFeature μ x (latitudeFrameAt x) p₀ s u
  have hi : Integrable (fun w : EuclideanBank n μ => Real.exp (β*inner ℝ v w))
      (stdGaussian (EuclideanBank n μ)) := by
    rw [← GaussianDensity.densityLaw_eq_stdGaussian]
    simpa only [real_inner_smul_left] using GaussianDensity.densityLaw_exp_integrable (β • v)
  have hcomp := (actual_bank_flattened_gaussian n μ).integrable_comp hi
  have h := hcomp.const_mul (Real.exp (amplitudeBasePotential μ β J δ q₁ q₂ x u))
  change Integrable (fun D : BankDisorder n μ =>
    Real.exp (amplitudeBasePotential μ β J δ q₁ q₂ x u)*Real.exp (β*inner ℝ v (euclideanBank D))) (bankLaw n μ) at h
  have he (D : BankDisorder n μ) :
      Real.exp (amplitudeBasePotential μ β J δ q₁ q₂ x u)*Real.exp (β*inner ℝ v (euclideanBank D))=
      Real.exp (β*amplitudePlantedField μ β x (latitudeFrameAt x) p₀ s D u-
        2*((n+1:ℕ):ℝ)*sourceProfile J δ q₁ q₂ (overlap x u)) := by
    rw [← Real.exp_add]
    have hh := amplitudeBankLinear_apply μ β x (latitudeFrameAt x) p₀ s u (euclideanBank D)
    rw [unpackBank_euclideanBank] at hh
    have hEval : β*inner ℝ v (euclideanBank D)=β*amplitudeField μ x (latitudeFrameAt x) p₀ s D u := by
      simpa only [amplitudeBankLinear,smul_apply,smul_eq_mul,innerSL_apply_apply,v] using hh
    rw [hEval]
    congr 1
    unfold amplitudeBasePotential amplitudePlantedField
    simp only [Nat.cast_add,Nat.cast_one]
    ring
  simpa only [he] using h

theorem amplitudeRestrictedPartition_measurable (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (E : Set (Vector (n+1))) : Measurable (amplitudeRestrictedPartition μ β J δ q₁ q₂ x p₀ s E) :=
  ((weightedPoint_measurable μ β J δ q₁ q₂ x p₀ s).stronglyMeasurable.integral_prod_right'
    (ν := (sphereLaw (n+1)).restrict E)).measurable

/-- True Tonelli budget for the actual restricted weighted partition. -/
theorem amplitudeRestrictedPartition_lintegral_le (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (hK : 0 ≤ sourceK J δ) (x : Vector (n+1)) (hx : ‖x‖^2=((n+1:ℕ):ℝ))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (hs : ∀ j,|s j|≤2)
    (E : Set (Vector (n+1))) :
    (∫⁻ D : BankDisorder n μ,ENNReal.ofReal (amplitudeRestrictedPartition μ β J δ q₁ q₂ x p₀ s E D)
      ∂bankLaw n μ)≤ENNReal.ofReal (Real.exp (3*β^2*((n+1:ℕ):ℝ)*μ.xi 1))*(sphereLaw (n+1)) E := by
  let f := fun z : BankDisorder n μ × Vector (n+1) => Real.exp
    (β*amplitudePlantedField μ β x (latitudeFrameAt x) p₀ s z.1 z.2-
      2*((n+1:ℕ):ℝ)*sourceProfile J δ q₁ q₂ (overlap x z.2))
  have hm : Measurable f := weightedPoint_measurable μ β J δ q₁ q₂ x p₀ s
  have hI (D : BankDisorder n μ) : Integrable (fun u => f (D,u)) ((sphereLaw (n+1)).restrict E) := by
    apply (integrable_sphere_of_continuous (by omega : 1≤n+1) ?_).restrict
    have hR : Continuous (fun u : Vector (n+1) => overlap x u) := by unfold overlap;fun_prop
    exact Real.continuous_exp.comp (((amplitudePlantedField_contDiff μ β x (latitudeFrameAt x) p₀ s D).continuous.const_mul β).sub
      (continuous_const.mul ((sourceProfile_contDiff J δ q₁ q₂).continuous.comp hR)))
  have he (D : BankDisorder n μ) : ENNReal.ofReal (amplitudeRestrictedPartition μ β J δ q₁ q₂ x p₀ s E D)=
      ∫⁻ u,ENNReal.ofReal (f (D,u)) ∂(sphereLaw (n+1)).restrict E :=
    ofReal_integral_eq_lintegral_ofReal (hI D) (.of_forall fun _ => (Real.exp_pos _).le)
  simp_rw [he]
  rw [lintegral_lintegral_swap hm.ennreal_ofReal.aemeasurable]
  have hPoint : ∀ᵐ u ∂(sphereLaw (n+1)).restrict E,
      (∫⁻ D : BankDisorder n μ,ENNReal.ofReal (f (D,u)) ∂bankLaw n μ)≤
        ENNReal.ofReal (Real.exp (3*β^2*((n+1:ℕ):ℝ)*μ.xi 1)) := by
    filter_upwards [ae_restrict_of_ae (sphereLaw_support (by omega : 1≤n+1))] with u hu
    rw [← ofReal_integral_eq_lintegral_ofReal (weightedPoint_bank_integrable μ β J δ q₁ q₂ x p₀ s u)
      (.of_forall fun _ => (Real.exp_pos _).le)]
    apply ENNReal.ofReal_le_ofReal
    exact amplitudeWeightedPoint_exp_integral_le μ β J δ q₁ q₂ hK x hx p₀ s hs u hu
  have hh := lintegral_mono_ae hPoint
  simpa only [lintegral_const,Measure.restrict_apply_univ] using hh

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
