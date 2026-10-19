module
public import QuantitativeFollowup.QuadraticTiltIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-! The actual second derivative of the logarithm of a bounded quadratic
tilt is variance minus the prescribed quadratic correction. This provides
the analytic, rather than postulated, variance term in the Prékopa route. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology
namespace QuantitativeFollowup

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
  (Kf Kg : ℝ) (hKf : 0 ≤ Kf) (hKg : 0 ≤ Kg)
  (hfb : ∀ x, |f x| ≤ Kf) (hgb : ∀ x, |g x| ≤ Kg)
include hf hg Kf Kg hKf hKg hfb hgb

theorem hasDerivAt_log_quadraticTiltIntegral (t : ℝ) :
    HasDerivAt (fun t => Real.log (∫ x, quadraticTiltWeight f g t x ∂P))
      ((∫ x, quadraticTiltSlope f g t x ∂P)/(∫ x, quadraticTiltWeight f g t x ∂P)) t := by
  apply (hasDerivAt_integral_quadraticTiltWeight P f g hf hg Kf Kg hKf hKg hfb hgb t).log
  exact (integral_exp_pos
    (integrable_quadraticTiltWeight P f g hf hg Kf Kg hKf hKg hfb hgb t)).ne'

theorem hasDerivAt_deriv_log_quadraticTiltIntegral (t : ℝ) :
    HasDerivAt (deriv (fun t => Real.log (∫ x, quadraticTiltWeight f g t x ∂P)))
      (((∫ x, quadraticTiltCurvature f g t x ∂P)*(∫ x, quadraticTiltWeight f g t x ∂P)-
        (∫ x, quadraticTiltSlope f g t x ∂P)^2)/(∫ x, quadraticTiltWeight f g t x ∂P)^2) t := by
  have hd := (hasDerivAt_integral_quadraticTiltSlope P f g hf hg Kf Kg hKf hKg hfb hgb t).div
    (hasDerivAt_integral_quadraticTiltWeight P f g hf hg Kf Kg hKf hKg hfb hgb t)
    (integral_exp_pos
      (integrable_quadraticTiltWeight P f g hf hg Kf Kg hKf hKg hfb hgb t)).ne'
  convert hd using 1
  · funext u
    exact (hasDerivAt_log_quadraticTiltIntegral P f g hf hg Kf Kg hKf hKg hfb hgb u).deriv
  · ring

theorem hasDerivAt_deriv_log_quadraticTiltIntegral_zero :
    HasDerivAt (deriv (fun t => Real.log (∫ x, quadraticTiltWeight f g t x ∂P)))
      (variance f P-∫ x, g x ∂P) 0 := by
  have hf2 : MemLp f 2 P := MemLp.of_bound hf.aestronglyMeasurable Kf
    (.of_forall fun x => by simpa only [Real.norm_eq_abs] using hfb x)
  have hg2 : MemLp g 2 P := MemLp.of_bound hg.aestronglyMeasurable Kg
    (.of_forall fun x => by simpa only [Real.norm_eq_abs] using hgb x)
  have hh := hasDerivAt_deriv_log_quadraticTiltIntegral P f g hf hg Kf Kg hKf hKg hfb hgb 0
  simp only [quadraticTiltCurvature,quadraticTiltSlope,quadraticTiltWeight,
    zero_mul,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_div,sub_zero,Real.exp_zero,
    mul_one,integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul,div_one,one_pow] at hh
  rw [integral_sub hf2.integrable_sq (hg2.integrable (by norm_num))] at hh
  rw [variance_eq_sub hf2]
  convert hh using 1
  · rfl
  · simp only [Pi.pow_apply]
    ring

theorem variance_le_of_concave_quadraticTilt (ε : ℝ) (hε : 0 < ε)
    (hc : ConcaveOn ℝ (Ioo (-ε) ε)
      (fun t => Real.log (∫ x, quadraticTiltWeight f g t x ∂P))) :
    variance f P ≤ ∫ x, g x ∂P := by
  have hA := hc.antitoneOn_deriv (fun t _ht =>
    (hasDerivAt_log_quadraticTiltIntegral P f g hf hg Kf Kg hKf hKg hfb hgb t).differentiableAt)
  have hn : derivWithin (deriv (fun t => Real.log (∫ x, quadraticTiltWeight f g t x ∂P)))
      (Ioo (-ε) ε) 0 ≤ 0 := hA.derivWithin_nonpos
  rw [derivWithin_of_mem_nhds (Ioo_mem_nhds (by linarith : -ε<0) hε),
    (hasDerivAt_deriv_log_quadraticTiltIntegral_zero P f g hf hg Kf Kg hKf hKg hfb hgb).deriv] at hn
  linarith

end QuantitativeFollowup
