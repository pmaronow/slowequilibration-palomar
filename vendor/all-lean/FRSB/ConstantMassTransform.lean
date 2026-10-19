module
public import FRSB.ForwardHeat
public import Paper.StateDiffusion
public import Paper.ParisiFiniteStep
public import Mathlib.Probability.Kernel.WithDensity

@[expose] public section

/-! The normalized constant-mass Gaussian h-transform.  These are actual
probability measures, including zero mass and zero elapsed variance. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open ColeHopfFoundation ColeHopfFoundation.ProbabilityTheory
open scoped NNReal ENNReal

namespace FRSB

def constantMassWeight (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ) (x y : ℝ) : ℝ :=
  Real.exp (m * (A y - coleHopf m v A x))

theorem constantMassWeight_pos (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ) (x y : ℝ) :
    0 < constantMassWeight m v A x y := Real.exp_pos _

theorem integrable_constantMassWeight (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ)
    (hA : HasLinearGrowth A) (hAm : Measurable A) (x : ℝ) :
    Integrable (constantMassWeight m v A x) (gaussianReal x v) := by
  have hshift : (gaussianReal 0 v).map (fun z => x + z) = gaussianReal x v := by
    simpa using (gaussianReal_map_const_add (μ := 0) (v := v) x)
  rw [← hshift, integrable_map_measure (by
    unfold constantMassWeight
    fun_prop) (by fun_prop)]
  by_cases hm : m = 0
  · subst m
    simpa [constantMassWeight, Function.comp_def] using (integrable_const (1 : ℝ) :
      Integrable (fun _ : ℝ => (1 : ℝ)) (gaussianReal 0 v))
  · exact integrable_coleHopfQ hA hAm hm v x

theorem integral_constantMassWeight (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ)
    (hA : HasLinearGrowth A) (hAm : Measurable A) (x : ℝ) :
    ∫ y, constantMassWeight m v A x y ∂gaussianReal x v = 1 := by
  have hshift : (gaussianReal 0 v).map (fun z => x + z) = gaussianReal x v := by
    simpa using (gaussianReal_map_const_add (μ := 0) (v := v) x)
  rw [← hshift, integral_map (by fun_prop) (by
    unfold constantMassWeight
    fun_prop)]
  by_cases hm : m = 0
  · simp [hm, constantMassWeight]
  · exact integral_coleHopfQ hA hAm hm v x

def constantMassTransition (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ) (x : ℝ) : Measure ℝ :=
  (gaussianReal x v).withDensity (fun y => ENNReal.ofReal (constantMassWeight m v A x y))

theorem isProbabilityMeasure_constantMassTransition (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ)
    (hA : HasLinearGrowth A) (hAm : Measurable A) (x : ℝ) :
    IsProbabilityMeasure (constantMassTransition m v A x) := ⟨by
  rw [constantMassTransition, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal
      (integrable_constantMassWeight m v A hA hAm x)
      (Filter.Eventually.of_forall fun y => (constantMassWeight_pos m v A x y).le),
    integral_constantMassWeight m v A hA hAm x]
  simp⟩

theorem integral_constantMassTransition (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ)
    (hA : HasLinearGrowth A) (hAm : Measurable A) (x : ℝ) (f : ℝ → ℝ) :
    ∫ y, f y ∂constantMassTransition m v A x =
      ∫ y, f y * constantMassWeight m v A x y ∂gaussianReal x v := by
  unfold constantMassTransition
  have hwm : Measurable (constantMassWeight m v A x) := by
    unfold constantMassWeight
    fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul]
  · congr 1
    funext y
    rw [ENNReal.toReal_ofReal (constantMassWeight_pos m v A x y).le, smul_eq_mul]
    ring
  · exact hwm.ennreal_ofReal
  · exact Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top

def constantMassDensity (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ) (x y : ℝ) : ℝ :=
  gaussianPDFReal x v y * constantMassWeight m v A x y

theorem integral_constantMassDensity (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (A : ℝ → ℝ) (hA : HasLinearGrowth A) (hAm : Measurable A) (x : ℝ) :
    ∫ y, constantMassDensity m v A x y = 1 := by
  have hi := integral_constantMassWeight m v A hA hAm x
  rw [integral_gaussianReal_eq_integral_smul hv] at hi
  simpa only [constantMassDensity, smul_eq_mul] using hi

theorem constantMassDensity_eq (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ) (x y : ℝ) :
    constantMassDensity m v A x y =
      Real.exp (m * A y) * heatDensity v (y - x) *
        Real.exp (-m * coleHopf m v A x) := by
  rw [constantMassDensity, constantMassWeight, gaussianPDFReal]
  unfold heatDensity
  rw [mul_sub, Real.exp_sub, neg_mul, Real.exp_neg]
  ring

end FRSB
