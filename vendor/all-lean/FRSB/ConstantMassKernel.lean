module
public import FRSB.ConstantMassTransform
public import Mathlib.Probability.Kernel.MeasurableIntegral
public import Mathlib.Probability.Kernel.Integral

@[expose] public section

/-! The genuine measurable Markov kernel for the constant-mass Cole-Hopf step. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open ColeHopfFoundation ColeHopfFoundation.ProbabilityTheory
open scoped NNReal ENNReal
namespace FRSB

theorem continuous_constantMassWeight (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ)
    (hAc : Continuous A) (hAg : HasLinearGrowth A) :
    Continuous (Function.uncurry (constantMassWeight m v A)) := by
  have hc : Continuous (fun x : ℝ => coleHopf m v A x) := by
    have hh := (continuous_coleHopf hAc hAg m).comp
      (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ => (v : ℝ))))
    convert! hh using 1
    funext x
    simp only [Function.comp_def, id_eq, Real.toNNReal_coe]
  convert! Real.continuous_exp.comp
    (((hAc.comp continuous_snd).sub (hc.comp continuous_fst)).const_mul m) using 1

def constantMassKernel (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ) : Kernel ℝ ℝ :=
  Kernel.withDensity (gaussianStateKernel v)
    (fun x y => ENNReal.ofReal (constantMassWeight m v A x y))

theorem constantMassKernel_apply (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ)
    (hAc : Continuous A) (hAg : HasLinearGrowth A) (x : ℝ) :
    constantMassKernel m v A x = constantMassTransition m v A x := by
  exact Kernel.withDensity_apply _
    (continuous_constantMassWeight m v A hAc hAg).measurable.ennreal_ofReal x

theorem isMarkovKernel_constantMassKernel (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ)
    (hAc : Continuous A) (hAg : HasLinearGrowth A) :
    IsMarkovKernel (constantMassKernel m v A) := by
  constructor
  intro x
  rw [constantMassKernel_apply m v A hAc hAg]
  exact isProbabilityMeasure_constantMassTransition m v A hAg hAc.measurable x

theorem integral_constantMassKernel (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ)
    (hAc : Continuous A) (hAg : HasLinearGrowth A) (x : ℝ) (f : ℝ → ℝ) :
    (∫ y, f y ∂constantMassKernel m v A x) =
      ∫ y, f y * constantMassWeight m v A x y ∂gaussianReal x v := by
  rw [constantMassKernel_apply m v A hAc hAg]
  exact integral_constantMassTransition m v A hAg hAc.measurable x f

theorem lintegral_constantMassKernel (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ)
    (hAc : Continuous A) (hAg : HasLinearGrowth A) (x : ℝ) (f : ℝ → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ y, f y ∂constantMassKernel m v A x) =
      ∫⁻ y, ENNReal.ofReal (constantMassWeight m v A x y) * f y ∂gaussianReal x v :=
  Kernel.lintegral_withDensity _
    (continuous_constantMassWeight m v A hAc hAg).measurable.ennreal_ofReal x hf

theorem constantMassKernel_zero_mass (v : ℝ≥0) (A : ℝ → ℝ)
    (hAc : Continuous A) (hAg : HasLinearGrowth A) :
    constantMassKernel 0 v A = gaussianStateKernel v := by
  ext x : 1
  rw [constantMassKernel_apply 0 v A hAc hAg]
  simp only [constantMassTransition, constantMassWeight, zero_mul, Real.exp_zero,
    ENNReal.ofReal_one, withDensity_one, gaussianStateKernel_apply]
  convert! (withDensity_one (μ := gaussianReal x v)) using 1

theorem constantMassKernel_zero_variance (m : ℝ) (A : ℝ → ℝ)
    (hAc : Continuous A) (hAg : HasLinearGrowth A) :
    constantMassKernel m 0 A = Kernel.id := by
  ext x : 1
  rw [constantMassKernel_apply m 0 A hAc hAg]
  simp only [constantMassTransition, gaussianReal_zero_var, constantMassWeight,
    coleHopf_zero_var, dirac_withDensity, sub_self, mul_zero, Real.exp_zero,
    ENNReal.ofReal_one, one_smul, Kernel.id_apply]

theorem integrable_constantMassKernel_bounded (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ)
    (hAc : Continuous A) (hAg : HasLinearGrowth A) (x : ℝ) (f : ℝ → ℝ)
    (hf : Measurable f) (C : ℝ) (hC : ∀ y, ‖f y‖ ≤ C) :
    Integrable f (constantMassKernel m v A x) := by
  letI := isMarkovKernel_constantMassKernel m v A hAc hAg
  exact (integrable_const C).mono' hf.aestronglyMeasurable (.of_forall hC)

theorem norm_integral_constantMassKernel_le (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ)
    (hAc : Continuous A) (hAg : HasLinearGrowth A) (x : ℝ) (f : ℝ → ℝ)
    (C : ℝ) (hC : ∀ y, ‖f y‖ ≤ C) :
    ‖∫ y, f y ∂constantMassKernel m v A x‖ ≤ C := by
  letI := isMarkovKernel_constantMassKernel m v A hAc hAg
  simpa using norm_integral_le_of_norm_le_const (μ := constantMassKernel m v A x)
    (.of_forall hC)

theorem stronglyMeasurable_integral_constantMassKernel (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ)
    (hAc : Continuous A) (hAg : HasLinearGrowth A) (f : ℝ → ℝ) (hf : Measurable f) :
    StronglyMeasurable (fun x => ∫ y, f y ∂constantMassKernel m v A x) := by
  letI := isMarkovKernel_constantMassKernel m v A hAc hAg
  exact ((hf.comp measurable_snd).stronglyMeasurable).integral_kernel_prod_right'

theorem integral_constantMassKernel_comp_bounded (P : Measure ℝ) [IsFiniteMeasure P]
    (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ) (hAc : Continuous A) (hAg : HasLinearGrowth A)
    (f : ℝ → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ y, ‖f y‖ ≤ C) :
    (∫ y, f y ∂(constantMassKernel m v A ∘ₘ P)) =
      ∫ x, (∫ y, f y ∂constantMassKernel m v A x) ∂P := by
  letI := isMarkovKernel_constantMassKernel m v A hAc hAg
  have hi : Integrable f (constantMassKernel m v A ∘ₘ P) :=
    (integrable_const C).mono' hf.aestronglyMeasurable (.of_forall hC)
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  rw [Kernel.integral_comp hi]
  rfl

end FRSB
