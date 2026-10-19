module
public import QuantitativePaper.VectorColeHopf
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

/-! Genuine differentiation of a Gaussian Cole--Hopf integral in a bounded
terminal-observable direction. Dominating functions are proved from the actual
Gaussian exponential moments, including the zero-mass branch. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal
namespace QuantitativePaper

def vectorStepResponse {n : ℕ} (c m : ℝ) (f v : Field n → ℝ) (x : Field n) : ℝ :=
  ∫ z,vectorStepWeight c m f x z*v (fieldShift c x z) ∂fieldGaussian n

theorem abs_vectorStepResponse_le {n : ℕ} (f v : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (c m R : ℝ) (hv : ∀ y,|v y| ≤ R) (x : Field n) :
    |vectorStepResponse c m f v x| ≤ R := by
  have hh := norm_integral_le_of_norm_le
    (f := fun z => vectorStepWeight c m f x z*v (fieldShift c x z))
    ((integrable_vectorStepWeight f K hf c m x).const_mul R)
    (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (vectorStepWeight_pos f K hf c m x z)]
      exact (mul_le_mul_of_nonneg_left (hv _) (vectorStepWeight_pos f K hf c m x z).le).trans_eq (by ring))
  rw [integral_const_mul,integral_vectorStepWeight f K hf c m x,mul_one] at hh
  exact hh

theorem hasDerivAt_vectorColeHopfStep_response {n : ℕ} (f v : ℝ → Field n → ℝ)
    (K R : ℝ≥0) (hf : ∀ y,LipschitzWith K (f y)) (hv : ∀ y,Measurable (v y))
    (hb : ∀ y z,|v y z| ≤ R) (hd : ∀ y z,HasDerivAt (fun r => f r z) (v y z) y)
    (c m : ℝ) (x : Field n) (y₀ : ℝ) :
    HasDerivAt (fun y => vectorColeHopfStep c m (f y) x)
      (vectorStepResponse c m (f y₀) (v y₀) x) y₀ := by
  have hshift : Continuous (fieldShift c x) := by unfold fieldShift;fun_prop
  have hparam (z : Field n) : LipschitzWith R (fun y => f y z) := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun y => (hd y z).differentiableAt)
    intro y
    rw [(hd y z).deriv,← NNReal.coe_le_coe]
    simpa only [coe_nnnorm,Real.norm_eq_abs] using hb y z
  by_cases hm : m = 0
  · subst m
    have hI := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun y z => f y (fieldShift c x z)) (F' := fun y z => v y (fieldShift c x z))
      (bound := fun _ => (R : ℝ)) (s := (univ : Set ℝ)) (by simp)
      (Eventually.of_forall fun y => ((hf y).continuous.comp hshift).aestronglyMeasurable)
      (integrable_vectorStep_input (f y₀) K (hf y₀) c x)
      ((hv y₀).comp hshift.measurable).aestronglyMeasurable
      (Eventually.of_forall fun z y _ => by simpa only [Real.norm_eq_abs] using hb y _)
      (integrable_const _) (Eventually.of_forall fun z y _ => hd y _)).2
    simpa [vectorColeHopfStep,vectorStepResponse,vectorStepWeight,vectorStepPartition] using hI
  · have hder (y : ℝ) (z : Field n) : HasDerivAt
        (fun r => Real.exp (m*f r (fieldShift c x z)))
        (Real.exp (m*f y (fieldShift c x z))*(m*v y (fieldShift c x z))) y := by
      exact ((hd y _).const_mul m).exp
    have hbound : ∀ z : Field n,∀ y ∈ Metric.ball y₀ 1,
        ‖Real.exp (m*f y (fieldShift c x z))*(m*v y (fieldShift c x z))‖ ≤
          (|m| * R*Real.exp (|m| * R))*Real.exp (m*f y₀ (fieldShift c x z)) := by
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
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _),abs_mul]
      calc
        _ ≤ Real.exp (m*f y (fieldShift c x z))*(|m| * R) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hb y _) (abs_nonneg m)) (Real.exp_pos _).le
        _ ≤ Real.exp (m*f y₀ (fieldShift c x z)+|m| * R)*(|m| * R) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hmf) (by positivity)
        _ = _ := by rw [Real.exp_add];ring
    have hI := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun y z => Real.exp (m*f y (fieldShift c x z)))
      (F' := fun y z => Real.exp (m*f y (fieldShift c x z))*(m*v y (fieldShift c x z)))
      (bound := fun z => (|m| * R*Real.exp (|m| * R))*Real.exp (m*f y₀ (fieldShift c x z)))
      (s := Metric.ball y₀ 1) (Metric.ball_mem_nhds y₀ (by norm_num))
      (Eventually.of_forall fun y => (Real.continuous_exp.comp
        (continuous_const.mul ((hf y).continuous.comp hshift))).aestronglyMeasurable)
      (integrable_exp_vectorStep (f y₀) K (hf y₀) c m x)
      ((Real.measurable_exp.comp (measurable_const.mul ((hf y₀).continuous.measurable.comp hshift.measurable))).mul
        (measurable_const.mul ((hv y₀).comp hshift.measurable))).aestronglyMeasurable
      (Eventually.of_forall hbound)
      ((integrable_exp_vectorStep (f y₀) K (hf y₀) c m x).const_mul _)
      (Eventually.of_forall fun z y _ => hder y z)).2
    have hlog := (hI.log (vectorStepPartition_pos (f y₀) K (hf y₀) c m x).ne').div_const m
    have heq : (∫ z,Real.exp (m*f y₀ (fieldShift c x z))*(m*v y₀ (fieldShift c x z)) ∂fieldGaussian n) =
        m*(∫ z,Real.exp (m*f y₀ (fieldShift c x z))*v y₀ (fieldShift c x z) ∂fieldGaussian n) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by ring
    rw [heq] at hlog
    have hresponse :
        (m*(∫ z,Real.exp (m*f y₀ (fieldShift c x z))*v y₀ (fieldShift c x z) ∂fieldGaussian n)/
          vectorStepPartition c m (f y₀) x)/m = vectorStepResponse c m (f y₀) (v y₀) x := by
      unfold vectorStepResponse vectorStepWeight
      have hrw : (fun z => (Real.exp (m*f y₀ (fieldShift c x z))/vectorStepPartition c m (f y₀) x)*
          v y₀ (fieldShift c x z)) = fun z =>
          (Real.exp (m*f y₀ (fieldShift c x z))*v y₀ (fieldShift c x z))/vectorStepPartition c m (f y₀) x := by
        funext z
        ring
      rw [hrw,integral_div]
      field_simp
    change HasDerivAt (fun y => Real.log (vectorStepPartition c m (f y) x)/m)
      ((m*(∫ z,Real.exp (m*f y₀ (fieldShift c x z))*v y₀ (fieldShift c x z) ∂fieldGaussian n)/
        vectorStepPartition c m (f y₀) x)/m) y₀ at hlog
    rw [hresponse] at hlog
    simpa only [vectorColeHopfStep,ite_eq_right hm,vectorStepPartition] using hlog

end QuantitativePaper
