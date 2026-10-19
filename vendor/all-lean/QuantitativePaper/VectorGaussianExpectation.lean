module
public import QuantitativePaper.VectorSecondResponse

@[expose] public section

/-! Positivity, linearity and variance of the actual normalized Gaussian
transition expectation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal
namespace QuantitativePaper

theorem vectorStepResponse_eq_transitionIntegral {n : ℕ} (f v : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (c m : ℝ) (x : Field n) :
    vectorStepResponse c m f v x = ∫ z,v (fieldShift c x z) ∂vectorStepTransition c m f x := by
  have hweight : Measurable (vectorStepWeight c m f x) := by
    unfold vectorStepWeight
    exact (Real.continuous_exp.comp (continuous_const.mul
      (hf.continuous.comp (show Continuous (fieldShift c x) from by unfold fieldShift;fun_prop)))).div_const _ |>.measurable
  unfold vectorStepTransition
  rw [integral_withDensity_eq_integral_toReal_smul hweight.ennreal_ofReal
    (Eventually.of_forall fun z => ENNReal.ofReal_lt_top) ]
  simp only [ENNReal.toReal_ofReal (vectorStepWeight_pos f K hf c m x _).le,smul_eq_mul]
  rfl

theorem integrable_vectorStepResponse_input {n : ℕ} (f v : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (hv : Measurable v) (R : ℝ) (hb : ∀ z,|v z| ≤ R)
    (c m : ℝ) (x : Field n) :
    Integrable (fun z => vectorStepWeight c m f x z*v (fieldShift c x z)) (fieldGaussian n) := by
  have he : (fun z => vectorStepWeight c m f x z*v (fieldShift c x z)) =
      fun z => (Real.exp (m*f (fieldShift c x z))*v (fieldShift c x z))/vectorStepPartition c m f x := by
    funext z
    unfold vectorStepWeight
    ring
  rw [he]
  exact (integrable_exp_vectorStep_mul f v K hf hv R hb c m x).div_const _

theorem vectorStepResponse_variance_nonneg {n : ℕ} (f v : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (hv : Measurable v) (R : ℝ) (hb : ∀ z,|v z| ≤ R)
    (c m : ℝ) (x : Field n) :
    0 ≤ vectorStepResponse c m f (fun z => v z^2) x-(vectorStepResponse c m f v x)^2 := by
  have := isProbabilityMeasure_vectorStepTransition f K hf c m x
  have hs : Measurable (fieldShift c x) := by unfold fieldShift;fun_prop
  have hv2 : MemLp (fun z => v (fieldShift c x z)) 2 (vectorStepTransition c m f x) :=
    MemLp.of_bound (hv.comp hs).aestronglyMeasurable R
      (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hb (fieldShift c x z))
  rw [vectorStepResponse_eq_transitionIntegral f _ K hf c m x,
    vectorStepResponse_eq_transitionIntegral f v K hf c m x]
  have hvar := variance_nonneg (fun z => v (fieldShift c x z)) (vectorStepTransition c m f x)
  rw [variance_eq_sub hv2] at hvar
  simpa only [Pi.pow_apply] using hvar

theorem vectorStepResponse_const {n : ℕ} (f : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (c m a : ℝ) (x : Field n) :
    vectorStepResponse c m f (fun _ => a) x = a := by
  unfold vectorStepResponse
  rw [integral_mul_const,integral_vectorStepWeight f K hf c m x,one_mul]

theorem vectorStepResponse_mul_const {n : ℕ} (f v : Field n → ℝ) (c m a : ℝ) (x : Field n) :
    vectorStepResponse c m f (fun z => a*v z) x = a*vectorStepResponse c m f v x := by
  unfold vectorStepResponse
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by ring

theorem vectorStepResponse_add {n : ℕ} (f v w : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (hv : Measurable v) (hw : Measurable w) (R S : ℝ)
    (hbv : ∀ z,|v z| ≤ R) (hbw : ∀ z,|w z| ≤ S) (c m : ℝ) (x : Field n) :
    vectorStepResponse c m f (fun z => v z+w z) x =
      vectorStepResponse c m f v x+vectorStepResponse c m f w x := by
  unfold vectorStepResponse
  simp_rw [mul_add]
  exact integral_add (integrable_vectorStepResponse_input f v K hf hv R hbv c m x)
    (integrable_vectorStepResponse_input f w K hf hw S hbw c m x)

theorem vectorStepResponse_sub {n : ℕ} (f v w : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (hv : Measurable v) (hw : Measurable w) (R S : ℝ)
    (hbv : ∀ z,|v z| ≤ R) (hbw : ∀ z,|w z| ≤ S) (c m : ℝ) (x : Field n) :
    vectorStepResponse c m f (fun z => v z-w z) x =
      vectorStepResponse c m f v x-vectorStepResponse c m f w x := by
  unfold vectorStepResponse
  simp_rw [mul_sub]
  exact integral_sub (integrable_vectorStepResponse_input f v K hf hv R hbv c m x)
    (integrable_vectorStepResponse_input f w K hf hw S hbw c m x)

theorem vectorStepResponse_mono {n : ℕ} (f v w : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (hv : Measurable v) (hw : Measurable w) (R S : ℝ)
    (hbv : ∀ z,|v z| ≤ R) (hbw : ∀ z,|w z| ≤ S) (hle : ∀ z,v z ≤ w z)
    (c m : ℝ) (x : Field n) : vectorStepResponse c m f v x ≤ vectorStepResponse c m f w x := by
  apply integral_mono (integrable_vectorStepResponse_input f v K hf hv R hbv c m x)
    (integrable_vectorStepResponse_input f w K hf hw S hbw c m x)
  intro z
  exact mul_le_mul_of_nonneg_left (hle _) (vectorStepWeight_pos f K hf c m x z).le

theorem vectorStepResponse_nonneg {n : ℕ} (f v : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (hv : ∀ z,0 ≤ v z) (c m : ℝ) (x : Field n) :
    0 ≤ vectorStepResponse c m f v x :=
  integral_nonneg fun z => mul_nonneg (vectorStepWeight_pos f K hf c m x z).le (hv _)

end QuantitativePaper
