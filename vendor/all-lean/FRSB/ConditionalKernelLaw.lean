module
public import FRSB.ConstantMassKernel
public import Paper.DiracConditionalLaw
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

@[expose] public section

/-! Fourier identification of conditional kernels from genuine weighted Itô identities. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped ENNReal NNReal
namespace FRSB

theorem stronglyMeasurable_kernelObservable (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    (f : ℝ → ℝ) (hf : Measurable f) :
    StronglyMeasurable (fun x => ∫ y, f y ∂κ x) :=
  ((hf.comp measurable_snd).stronglyMeasurable).integral_kernel_prod_right'

theorem integral_kernel_comp_bounded (P : Measure ℝ) [IsFiniteMeasure P]
    (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] (f : ℝ → ℝ)
    (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    (∫ y, f y ∂(κ ∘ₘ P)) = ∫ x, (∫ y, f y ∂κ x) ∂P := by
  have hi : Integrable f (κ ∘ₘ P) :=
    (integrable_const C).mono' hf.aestronglyMeasurable (.of_forall hC)
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  rw [Kernel.integral_comp hi]
  rfl

theorem integral_indicator_one_mul_eq_setIntegral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω) (hA : MeasurableSet A) (f : Ω → ℝ) :
    (∫ sample, A.indicator (fun _ => (1 : ℝ)) sample * f sample ∂P) =
      ∫ sample in A, f sample ∂P := by
  rw [← integral_indicator hA]
  apply integral_congr_ae
  exact .of_forall fun sample => by
    by_cases hsample : sample ∈ A <;> simp [hsample]

theorem restricted_transitionLaw_of_weighted_fourier {Ω : Type*} (m₀ : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hm₀ : m₀ ≤ mΩ)
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    (hcos : ∀ (ξ : ℝ) (Z : Ω → ℝ), StronglyMeasurable[m₀] Z →
      (∀ sample, ‖Z sample‖ ≤ (1 : ℝ)) →
      (∫ sample, Z sample * Real.cos (ξ * Y sample) ∂P) =
        ∫ sample, Z sample * (∫ y, Real.cos (ξ*y) ∂κ (X sample)) ∂P)
    (hsin : ∀ (ξ : ℝ) (Z : Ω → ℝ), StronglyMeasurable[m₀] Z →
      (∀ sample, ‖Z sample‖ ≤ (1 : ℝ)) →
      (∫ sample, Z sample * Real.sin (ξ * Y sample) ∂P) =
        ∫ sample, Z sample * (∫ y, Real.sin (ξ*y) ∂κ (X sample)) ∂P)
    (A : Set Ω) (hA : MeasurableSet[m₀] A) :
    (P.restrict A).map Y = κ ∘ₘ (P.restrict A).map X := by
  have hAg : MeasurableSet A := hm₀ A hA
  have hZ : StronglyMeasurable[m₀] (A.indicator (fun _ => (1 : ℝ))) :=
    stronglyMeasurable_const.indicator hA
  have hZb : ∀ sample, ‖A.indicator (fun _ => (1 : ℝ)) sample‖ ≤ (1 : ℝ) := by
    intro sample
    by_cases hsample : sample ∈ A <;> simp [hsample]
  apply measure_eq_of_cos_sin_integrals
  · intro ξ
    have he := hcos ξ _ hZ hZb
    rw [integral_indicator_one_mul_eq_setIntegral P A hAg,
      integral_indicator_one_mul_eq_setIntegral P A hAg] at he
    rw [integral_map hY.aemeasurable (by fun_prop : AEStronglyMeasurable
      (fun y : ℝ => Real.cos (ξ*y)) ((P.restrict A).map Y)),
      integral_kernel_comp_bounded _ κ (fun y => Real.cos (ξ*y)) (by fun_prop) 1
        (fun y => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (ξ*y)),
      integral_map hX.aemeasurable
        (stronglyMeasurable_kernelObservable κ _ (by fun_prop)).aestronglyMeasurable]
    exact he
  · intro ξ
    have he := hsin ξ _ hZ hZb
    rw [integral_indicator_one_mul_eq_setIntegral P A hAg,
      integral_indicator_one_mul_eq_setIntegral P A hAg] at he
    rw [integral_map hY.aemeasurable (by fun_prop : AEStronglyMeasurable
      (fun y : ℝ => Real.sin (ξ*y)) ((P.restrict A).map Y)),
      integral_kernel_comp_bounded _ κ (fun y => Real.sin (ξ*y)) (by fun_prop) 1
        (fun y => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (ξ*y)),
      integral_map hX.aemeasurable
        (stronglyMeasurable_kernelObservable κ _ (by fun_prop)).aestronglyMeasurable]
    exact he

theorem condExp_kernel_of_restricted_transitionLaw {Ω : Type*} (m₀ : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hm₀ : m₀ ≤ mΩ)
    (X Y : Ω → ℝ) (hX : StronglyMeasurable[m₀] X) (hY : Measurable Y)
    (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    (hlaw : ∀ A : Set Ω, MeasurableSet[m₀] A → (P.restrict A).map Y =
      κ ∘ₘ (P.restrict A).map X)
    (f : ℝ → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    P[(fun sample => f (Y sample)) | m₀] =ᵐ[P]
      fun sample => ∫ y, f y ∂κ (X sample) := by
  have hkernel := stronglyMeasurable_kernelObservable κ f hf
  have hcand : StronglyMeasurable[m₀] (fun sample => ∫ y, f y ∂κ (X sample)) :=
    hkernel.comp_measurable hX.measurable
  have hi : Integrable (fun sample => f (Y sample)) P :=
    (integrable_const C).mono' (hf.comp hY).aestronglyMeasurable (.of_forall fun sample => hC _)
  have hci : Integrable (fun sample => ∫ y, f y ∂κ (X sample)) P :=
    (integrable_const C).mono' (hcand.mono hm₀).aestronglyMeasurable (.of_forall fun sample => by
      simpa using norm_integral_le_of_norm_le_const (μ := κ (X sample)) (.of_forall hC))
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm₀ hi
  · intro A hA hfinite
    exact hci.integrableOn
  · intro A hA hfinite
    have he : (∫ y, f y ∂(P.restrict A).map Y) =
        ∫ y, f y ∂(κ ∘ₘ (P.restrict A).map X) := by rw [hlaw A hA]
    rw [integral_map hY.aemeasurable hf.aestronglyMeasurable,
      integral_kernel_comp_bounded _ κ f hf C hC,
      integral_map (hX.mono hm₀).measurable.aemeasurable hkernel.aestronglyMeasurable] at he
    exact he.symm
  · exact hcand.aestronglyMeasurable

theorem weighted_kernelObservable_of_condExp {Ω : Type*} (m₀ : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hm₀ : m₀ ≤ mΩ)
    (g k : Ω → ℝ) (hg : Integrable g P) (hcond : P[g | m₀] =ᵐ[P] k)
    (Z : Ω → ℝ) (hZ : StronglyMeasurable[m₀] Z) (CZ : ℝ)
    (hZb : ∀ sample, ‖Z sample‖ ≤ CZ) :
    (∫ sample, Z sample * g sample ∂P) = ∫ sample, Z sample * k sample ∂P := by
  have hpull := condExp_stronglyMeasurable_mul_of_bound hm₀ hZ hg CZ (.of_forall hZb)
  have hprod : (fun sample => Z sample * P[g | m₀] sample) =ᵐ[P]
      fun sample => Z sample * k sample := by
    filter_upwards [hcond] with sample hsample
    rw [hsample]
  have he := integral_congr_ae (hpull.trans hprod)
  rw [integral_condExp hm₀] at he
  exact he

end FRSB
