module
public import QuantitativePaper.VectorResponse

@[expose] public section

/-! Actual second differentiation of the normalized Gaussian response. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal
namespace QuantitativePaper

theorem vectorStepResponse_eq_quotient {n : ℕ} (c m : ℝ) (f v : Field n → ℝ) (x : Field n) :
    vectorStepResponse c m f v x =
      (∫ z,Real.exp (m*f (fieldShift c x z))*v (fieldShift c x z) ∂fieldGaussian n)/
        vectorStepPartition c m f x := by
  unfold vectorStepResponse vectorStepWeight
  have he : (fun z => Real.exp (m*f (fieldShift c x z))/vectorStepPartition c m f x*v (fieldShift c x z)) =
      fun z => (Real.exp (m*f (fieldShift c x z))*v (fieldShift c x z))/vectorStepPartition c m f x := by
    funext z
    ring
  rw [he,integral_div]

theorem integrable_exp_vectorStep_mul {n : ℕ} (f v : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (hv : Measurable v) (R : ℝ) (hb : ∀ z,|v z| ≤ R)
    (c m : ℝ) (x : Field n) :
    Integrable (fun z => Real.exp (m*f (fieldShift c x z))*v (fieldShift c x z)) (fieldGaussian n) := by
  have hs : Continuous (fieldShift c x) := by unfold fieldShift;fun_prop
  apply ((integrable_exp_vectorStep f K hf c m x).const_mul R).mono'
    ((Real.continuous_exp.comp (continuous_const.mul (hf.continuous.comp hs))).measurable.mul
      (hv.comp hs.measurable)).aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    dsimp only [Function.comp_apply,Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (m*f (fieldShift c x z))*R := mul_le_mul_of_nonneg_left (hb _) (Real.exp_pos _).le
      _ = _ := by ring

def vectorStepSecondResponse {n : ℕ} (c m : ℝ) (f v w : Field n → ℝ) (x : Field n) : ℝ :=
  vectorStepResponse c m f w x+m*(vectorStepResponse c m f (fun z => v z^2) x-
    vectorStepResponse c m f v x^2)


theorem abs_vectorStepSecondResponse_le {n : ℕ} (f v w : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (R S : ℝ≥0) (hbv : ∀ z,|v z| ≤ R) (hbw : ∀ z,|w z| ≤ S)
    (c m : ℝ) (x : Field n) :
    |vectorStepSecondResponse c m f v w x| ≤ (S : ℝ)+2*|m| * (R : ℝ)^2 := by
  have hR := abs_vectorStepResponse_le f v K hf c m R hbv x
  have hR2 : vectorStepResponse c m f v x^2 ≤ (R : ℝ)^2 := by
    have hh := mul_self_le_mul_self (abs_nonneg _) hR
    simpa [←pow_two] using hh
  have hv2 : ∀ z,|v z^2| ≤ (R : ℝ)^2 := by
    intro z
    rw [abs_of_nonneg (sq_nonneg _)]
    have hh := mul_self_le_mul_self (abs_nonneg _) (hbv z)
    simpa [←pow_two] using hh
  have hV2 := abs_vectorStepResponse_le f (fun z => v z^2) K hf c m ((R : ℝ)^2) hv2 x
  have hW := abs_vectorStepResponse_le f w K hf c m S hbw x
  unfold vectorStepSecondResponse
  calc
    _ ≤ |vectorStepResponse c m f w x|+|m*(vectorStepResponse c m f (fun z => v z^2) x-vectorStepResponse c m f v x^2)| := abs_add_le _ _
    _ ≤ S+|m| * (|vectorStepResponse c m f (fun z => v z^2) x|+vectorStepResponse c m f v x^2) := by
      rw [abs_mul]
      apply add_le_add hW
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg m)
      have ha := abs_add_le (vectorStepResponse c m f (fun z => v z^2) x)
        (-((vectorStepResponse c m f v x)^2))
      rw [abs_neg,abs_sq] at ha
      simpa only [sub_eq_add_neg] using ha
    _ ≤ S+|m| * ((R : ℝ)^2+(R : ℝ)^2) :=
      add_le_add (le_refl (S : ℝ)) (mul_le_mul_of_nonneg_left (add_le_add hV2 hR2) (abs_nonneg m))
    _ = _ := by ring

theorem vectorStepPartition_eq_exp {n : ℕ} (f : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (c m : ℝ) (x : Field n) :
    vectorStepPartition c m f x = Real.exp (m*vectorColeHopfStep c m f x) := by
  by_cases hm : m = 0
  · simp [vectorStepPartition,hm]
  · unfold vectorColeHopfStep
    rw [ite_eq_right hm,mul_div_cancel₀ _ hm,Real.exp_log (vectorStepPartition_pos f K hf c m x)]

theorem hasDerivAt_vectorStepResponse {n : ℕ} (f v w : ℝ → Field n → ℝ)
    (K R S : ℝ≥0) (hf : ∀ y,LipschitzWith K (f y))
    (hv : ∀ y,Measurable (v y)) (hw : ∀ y,Measurable (w y))
    (hbv : ∀ y z,|v y z| ≤ R) (hbw : ∀ y z,|w y z| ≤ S)
    (hdf : ∀ y z,HasDerivAt (fun r => f r z) (v y z) y)
    (hdv : ∀ y z,HasDerivAt (fun r => v r z) (w y z) y)
    (c m : ℝ) (x : Field n) (y₀ : ℝ) :
    HasDerivAt (fun y => vectorStepResponse c m (f y) (v y) x)
      (vectorStepSecondResponse c m (f y₀) (v y₀) (w y₀) x) y₀ := by
  have hs : Continuous (fieldShift c x) := by unfold fieldShift;fun_prop
  have hparam (z : Field n) : LipschitzWith R (fun y => f y z) := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun y => (hdf y z).differentiableAt)
    intro y
    rw [(hdf y z).deriv,← NNReal.coe_le_coe]
    simpa only [coe_nnnorm,Real.norm_eq_abs] using hbv y z
  have hder (y : ℝ) (z : Field n) : HasDerivAt
      (fun r => Real.exp (m*f r (fieldShift c x z))*v r (fieldShift c x z))
      (Real.exp (m*f y (fieldShift c x z))*(m*v y (fieldShift c x z)^2+w y (fieldShift c x z))) y := by
    convert (((hdf y _).const_mul m).exp).mul (hdv y _) using 1
    ring
  have hbound : ∀ z : Field n,∀ y ∈ Metric.ball y₀ 1,
      ‖Real.exp (m*f y (fieldShift c x z))*(m*v y (fieldShift c x z)^2+w y (fieldShift c x z))‖ ≤
        ((|m| * (R : ℝ)^2+S)*Real.exp (|m| * R))*Real.exp (m*f y₀ (fieldShift c x z)) := by
    intro z y hy
    have hdist : dist y y₀ < 1 := hy
    have hdiff := (hparam (fieldShift c x z)).dist_le_mul y y₀
    rw [Real.dist_eq] at hdiff
    have hmf : m*f y (fieldShift c x z) ≤ m*f y₀ (fieldShift c x z)+|m| * R := by
      have hp := mul_le_mul_of_nonneg_left
        (hdiff.trans (mul_le_mul_of_nonneg_left hdist.le R.coe_nonneg)) (abs_nonneg m)
      have hmul := le_abs_self (m*(f y (fieldShift c x z)-f y₀ (fieldShift c x z)))
      rw [abs_mul] at hmul
      linarith
    have hv2 : v y (fieldShift c x z)^2 ≤ (R : ℝ)^2 := by
      have hh := mul_self_le_mul_self (abs_nonneg _) (hbv y (fieldShift c x z))
      simpa [←pow_two] using hh
    have hinner : |m*v y (fieldShift c x z)^2+w y (fieldShift c x z)| ≤ |m| * (R : ℝ)^2+S := by
      calc
        _ ≤ |m*v y (fieldShift c x z)^2|+|w y (fieldShift c x z)| := abs_add_le _ _
        _ = |m| * v y (fieldShift c x z)^2+|w y (fieldShift c x z)| := by rw [abs_mul,abs_of_nonneg (sq_nonneg (v y (fieldShift c x z)))]
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hv2 (abs_nonneg m)) (hbw y _)
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (m*f y (fieldShift c x z))*(|m| * (R : ℝ)^2+S) :=
        mul_le_mul_of_nonneg_left hinner (Real.exp_pos _).le
      _ ≤ Real.exp (m*f y₀ (fieldShift c x z)+|m| * R)*(|m| * (R : ℝ)^2+S) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hmf) (by positivity)
      _ = _ := by rw [Real.exp_add];ring
  have hI := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y z => Real.exp (m*f y (fieldShift c x z))*v y (fieldShift c x z))
    (F' := fun y z => Real.exp (m*f y (fieldShift c x z))*(m*v y (fieldShift c x z)^2+w y (fieldShift c x z)))
    (bound := fun z => ((|m| * (R : ℝ)^2+S)*Real.exp (|m| * R))*Real.exp (m*f y₀ (fieldShift c x z)))
    (s := Metric.ball y₀ 1) (Metric.ball_mem_nhds y₀ (by norm_num))
    (Eventually.of_forall fun y => ((Real.continuous_exp.comp
      (continuous_const.mul ((hf y).continuous.comp hs))).measurable.mul
      ((hv y).comp hs.measurable)).aestronglyMeasurable)
    (integrable_exp_vectorStep_mul (f y₀) (v y₀) K (hf y₀) (hv y₀) R (hbv y₀) c m x)
    ((Real.continuous_exp.comp (continuous_const.mul ((hf y₀).continuous.comp hs))).measurable.mul
      ((measurable_const.mul (((hv y₀).comp hs.measurable).pow_const 2)).add ((hw y₀).comp hs.measurable))).aestronglyMeasurable
    (Eventually.of_forall hbound)
    ((integrable_exp_vectorStep (f y₀) K (hf y₀) c m x).const_mul _)
    (Eventually.of_forall fun z y _ => hder y z)).2
  have hG := hasDerivAt_vectorColeHopfStep_response f v K R hf hv hbv hdf c m x y₀
  have hZ : HasDerivAt (fun y => vectorStepPartition c m (f y) x)
      (vectorStepPartition c m (f y₀) x*(m*vectorStepResponse c m (f y₀) (v y₀) x)) y₀ := by
    simpa only [← vectorStepPartition_eq_exp _ K (hf _) c m x] using (hG.const_mul m).exp
  have hiw := integrable_exp_vectorStep_mul (f y₀) (w y₀) K (hf y₀) (hw y₀) S (hbw y₀) c m x
  have hiv2 := integrable_exp_vectorStep_mul (f y₀) (fun z => v y₀ z^2) K (hf y₀)
    ((hv y₀).pow_const 2) ((R : ℝ)^2) (fun z => by
      rw [abs_of_nonneg (sq_nonneg _)]
      have hh := mul_self_le_mul_self (abs_nonneg _) (hbv y₀ z)
      simpa [←pow_two] using hh) c m x
  have hsplit : (∫ z,Real.exp (m*f y₀ (fieldShift c x z))*(m*v y₀ (fieldShift c x z)^2+w y₀ (fieldShift c x z)) ∂fieldGaussian n) =
      m*(∫ z,Real.exp (m*f y₀ (fieldShift c x z))*v y₀ (fieldShift c x z)^2 ∂fieldGaussian n)+
      (∫ z,Real.exp (m*f y₀ (fieldShift c x z))*w y₀ (fieldShift c x z) ∂fieldGaussian n) := by
    have he : (fun z => Real.exp (m*f y₀ (fieldShift c x z))*(m*v y₀ (fieldShift c x z)^2+w y₀ (fieldShift c x z))) =
        (fun z => m*(Real.exp (m*f y₀ (fieldShift c x z))*v y₀ (fieldShift c x z)^2))+
        (fun z => Real.exp (m*f y₀ (fieldShift c x z))*w y₀ (fieldShift c x z)) := by funext z;dsimp;ring
    rw [he]
    change (∫ z,m*(Real.exp (m*f y₀ (fieldShift c x z))*v y₀ (fieldShift c x z)^2)+
      Real.exp (m*f y₀ (fieldShift c x z))*w y₀ (fieldShift c x z) ∂fieldGaussian n) = _
    rw [integral_add (hiv2.const_mul m) hiw,integral_const_mul]
  have hquot := hI.div hZ (vectorStepPartition_pos (f y₀) K (hf y₀) c m x).ne'
  have hval : ((∫ z,Real.exp (m*f y₀ (fieldShift c x z))*(m*v y₀ (fieldShift c x z)^2+w y₀ (fieldShift c x z)) ∂fieldGaussian n)*
      vectorStepPartition c m (f y₀) x-
      (∫ z,Real.exp (m*f y₀ (fieldShift c x z))*v y₀ (fieldShift c x z) ∂fieldGaussian n)*
        (vectorStepPartition c m (f y₀) x*(m*vectorStepResponse c m (f y₀) (v y₀) x)))/
      vectorStepPartition c m (f y₀) x^2 = vectorStepSecondResponse c m (f y₀) (v y₀) (w y₀) x := by
    rw [hsplit]
    unfold vectorStepSecondResponse
    rw [vectorStepResponse_eq_quotient c m (f y₀) (w y₀) x,
      vectorStepResponse_eq_quotient c m (f y₀) (fun z => v y₀ z^2) x,
      vectorStepResponse_eq_quotient c m (f y₀) (v y₀) x]
    field_simp
    ring
  rw [hval] at hquot
  convert hquot using 1
  funext y
  exact vectorStepResponse_eq_quotient c m (f y) (v y) x

end QuantitativePaper
