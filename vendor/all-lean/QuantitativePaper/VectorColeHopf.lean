module
public import QuantitativePaper.VectorTerminal

@[expose] public section

/-! Genuine finite-dimensional Gaussian Cole--Hopf steps. Exponential moments,
normalization of the transition law, and preservation of the field Lipschitz
bound are proved from the actual Gaussian integrals. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal
namespace QuantitativePaper

def fieldShift {n : ℕ} (c : ℝ) (x z : Field n) : Field n := x+Real.sqrt c • z

def vectorStepPartition {n : ℕ} (c m : ℝ) (f : Field n → ℝ) (x : Field n) : ℝ :=
  ∫ z,Real.exp (m*f (fieldShift c x z)) ∂fieldGaussian n

def vectorColeHopfStep {n : ℕ} (c m : ℝ) (f : Field n → ℝ) (x : Field n) : ℝ :=
  if m = 0 then ∫ z,f (fieldShift c x z) ∂fieldGaussian n
  else Real.log (vectorStepPartition c m f x)/m

def vectorStepWeight {n : ℕ} (c m : ℝ) (f : Field n → ℝ) (x z : Field n) : ℝ :=
  Real.exp (m*f (fieldShift c x z))/vectorStepPartition c m f x

def vectorStepTransition {n : ℕ} (c m : ℝ) (f : Field n → ℝ) (x : Field n) : Measure (Field n) :=
  (fieldGaussian n).withDensity (fun z => ENNReal.ofReal (vectorStepWeight c m f x z))

theorem fieldShift_dist {n : ℕ} (c : ℝ) (x y z : Field n) :
    dist (fieldShift c x z) (fieldShift c y z) = dist x y := by
  simp [fieldShift,dist_eq_norm]

theorem abs_fieldShift_lipschitz {n : ℕ} (f : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (c : ℝ) (x z : Field n) :
    |f (fieldShift c x z)| ≤ |f x|+(K : ℝ)*Real.sqrt c*‖z‖ := by
  have hh := hf.dist_le_mul (fieldShift c x z) x
  simp only [dist_eq_norm,fieldShift,add_sub_cancel_left,norm_smul,
    Real.norm_of_nonneg (Real.sqrt_nonneg _),Real.norm_eq_abs] at hh
  calc
    |f (fieldShift c x z)| ≤ |f x|+|f (fieldShift c x z)-f x| := by
      have ha := norm_add_le (f x) (f (fieldShift c x z)-f x)
      simpa only [add_sub_cancel,Real.norm_eq_abs] using ha
    _ ≤ _ := by simpa only [fieldShift,mul_assoc] using add_le_add (le_refl |f x|) hh

theorem integrable_exp_vectorStep {n : ℕ} (f : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (c m : ℝ) (x : Field n) :
    Integrable (fun z => Real.exp (m*f (fieldShift c x z))) (fieldGaussian n) := by
  apply ((SYK.integrable_exp_mul_norm (ι := Fin n) (|m| * (K : ℝ)*Real.sqrt c)).const_mul
    (Real.exp (|m| * |f x|))).mono'
      (show AEStronglyMeasurable (fun z => Real.exp (m*f (fieldShift c x z))) (fieldGaussian n) from
        (Real.continuous_exp.comp (continuous_const.mul
          (hf.continuous.comp (by unfold fieldShift;fun_prop)))).aestronglyMeasurable)
  apply Eventually.of_forall
  intro z
  rw [Real.norm_of_nonneg (Real.exp_pos _).le,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  calc
    m*f (fieldShift c x z) ≤ |m| * |f (fieldShift c x z)| := by rw [← abs_mul];exact le_abs_self _
    _ ≤ |m| * (|f x|+(K : ℝ)*Real.sqrt c*‖z‖) :=
      mul_le_mul_of_nonneg_left (abs_fieldShift_lipschitz f K hf c x z) (abs_nonneg _)
    _ = _ := by ring

theorem integrable_vectorStep_input {n : ℕ} (f : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (c : ℝ) (x : Field n) :
    Integrable (fun z => f (fieldShift c x z)) (fieldGaussian n) := by
  apply (integrable_norm_iff (hf.continuous.comp (by unfold fieldShift;fun_prop)).aestronglyMeasurable).mp
  simpa only [Real.norm_eq_abs,pow_one,Function.comp_apply] using
    integrable_pow_abs_of_integrable_exp_mul one_ne_zero
      (integrable_exp_vectorStep f K hf c 1 x)
      (integrable_exp_vectorStep f K hf c (-1) x) 1

theorem vectorStepPartition_pos {n : ℕ} (f : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (c m : ℝ) (x : Field n) : 0 < vectorStepPartition c m f x := by
  apply (integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le)
    (integrable_exp_vectorStep f K hf c m x)).mpr
  have hs : Function.support (fun z => Real.exp (m*f (fieldShift c x z))) = univ := by
    ext z
    simp [Function.mem_support,Real.exp_ne_zero]
  rw [hs]
  simp

theorem vectorStepWeight_pos {n : ℕ} (f : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (c m : ℝ) (x z : Field n) : 0 < vectorStepWeight c m f x z :=
  div_pos (Real.exp_pos _) (vectorStepPartition_pos f K hf c m x)

theorem integrable_vectorStepWeight {n : ℕ} (f : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (c m : ℝ) (x : Field n) :
    Integrable (vectorStepWeight c m f x) (fieldGaussian n) :=
  (integrable_exp_vectorStep f K hf c m x).div_const _

theorem integral_vectorStepWeight {n : ℕ} (f : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (c m : ℝ) (x : Field n) :
    (∫ z,vectorStepWeight c m f x z ∂fieldGaussian n) = 1 := by
  unfold vectorStepWeight
  rw [integral_div,← vectorStepPartition,div_self (vectorStepPartition_pos f K hf c m x).ne']

theorem isProbabilityMeasure_vectorStepTransition {n : ℕ} (f : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (c m : ℝ) (x : Field n) :
    IsProbabilityMeasure (vectorStepTransition c m f x) := ⟨by
  rw [vectorStepTransition,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_vectorStepWeight f K hf c m x)
      (Eventually.of_forall fun z => (vectorStepWeight_pos f K hf c m x z).le),
    integral_vectorStepWeight f K hf c m x]
  norm_num⟩

theorem vectorStepWeight_eq_exp {n : ℕ} (f : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (c m : ℝ) (hm : m ≠ 0) (x z : Field n) :
    vectorStepWeight c m f x z =
      Real.exp (m*(f (fieldShift c x z)-vectorColeHopfStep c m f x)) := by
  unfold vectorStepWeight vectorColeHopfStep
  rw [ite_eq_right hm,mul_sub,mul_div_cancel₀ _ hm,Real.exp_sub,
    Real.exp_log (vectorStepPartition_pos f K hf c m x)]

private theorem vectorColeHopfStep_sub_le {n : ℕ} (f : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (c m : ℝ) (hm : 0 < m) (x y : Field n) :
    vectorColeHopfStep c m f x-vectorColeHopfStep c m f y ≤ (K : ℝ)*dist x y := by
  have hpt (z : Field n) : f (fieldShift c x z) ≤ f (fieldShift c y z)+(K : ℝ)*dist x y := by
    have hh := hf.dist_le_mul (fieldShift c x z) (fieldShift c y z)
    rw [Real.dist_eq,fieldShift_dist] at hh
    have hh2 := (abs_le.mp hh).2
    linarith
  have hsum : vectorStepPartition c m f x ≤
      Real.exp (m*((K : ℝ)*dist x y))*vectorStepPartition c m f y := by
    rw [vectorStepPartition,vectorStepPartition,← integral_const_mul]
    apply integral_mono (integrable_exp_vectorStep f K hf c m x)
      ((integrable_exp_vectorStep f K hf c m y).const_mul _)
    intro z
    calc
      _ ≤ Real.exp (m*(f (fieldShift c y z)+(K : ℝ)*dist x y)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hpt z) hm.le)
      _ = _ := by rw [mul_add,Real.exp_add];ring
  have hh := Real.log_le_log (vectorStepPartition_pos f K hf c m x) hsum
  rw [Real.log_mul (Real.exp_ne_zero _) (vectorStepPartition_pos f K hf c m y).ne',Real.log_exp] at hh
  unfold vectorColeHopfStep
  rw [ite_eq_right hm.ne',ite_eq_right hm.ne',← sub_div,div_le_iff₀ hm]
  linarith

theorem vectorColeHopfStep_lipschitz {n : ℕ} (f : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (c m : ℝ) (hm : 0 ≤ m) :
    LipschitzWith K (vectorColeHopfStep c m f) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [Real.dist_eq,abs_le]
  by_cases hm0 : m = 0
  · subst m
    simp only [vectorColeHopfStep,ite_true]
    rw [← integral_sub (integrable_vectorStep_input f K hf c x) (integrable_vectorStep_input f K hf c y)]
    have hb := norm_integral_le_of_norm_le_const
      (f := fun z : Field n => f (fieldShift c x z)-f (fieldShift c y z)) (μ := fieldGaussian n)
      (C := (K : ℝ)*dist x y) (Eventually.of_forall fun z => by
        have hh := hf.dist_le_mul (fieldShift c x z) (fieldShift c y z)
        simpa only [Real.dist_eq,Real.norm_eq_abs,fieldShift_dist] using hh)
    simpa [Real.norm_eq_abs,abs_le] using hb
  · have hpos := lt_of_le_of_ne hm (Ne.symm hm0)
    constructor
    · have hh := vectorColeHopfStep_sub_le f K hf c m hpos y x
      rw [dist_comm] at hh
      linarith
    · exact vectorColeHopfStep_sub_le f K hf c m hpos x y

end QuantitativePaper
