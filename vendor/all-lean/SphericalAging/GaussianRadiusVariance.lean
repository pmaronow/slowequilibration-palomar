module

public import SphericalAging.DifferentiableGaussianVariance
public import Mathlib.Analysis.InnerProductSpace.Calculus

public section

/-! True Gaussian radius estimates used for the literal normalized
Gaussian initial sphere law. The variance estimate follows from the
proved Gaussian rotation inequality; no radius-concentration premise is
assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace BigOperators ENNReal
namespace SphericalAging.GaussianRadiusVariance
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

 lemma integral_norm_sq : (∫ x : E,‖x‖^2 ∂stdGaussian E)=(Module.finrank ℝ E : ℝ) := by
  let b := stdOrthonormalBasis ℝ E
  have he : (fun x : E => ‖x‖^2)=fun x => ∑ i : Fin (Module.finrank ℝ E),‖inner ℝ (b i) x‖^2 := by
    funext x
    exact (b.sum_sq_norm_inner_right x).symm
  have hi (i : Fin (Module.finrank ℝ E)) : Integrable (fun x : E => ‖inner ℝ (b i) x‖^2) (stdGaussian E) := by
    simpa only [Real.norm_eq_abs,sq_abs,innerSL_apply_apply,id_eq] using
      ((IsGaussian.memLp_two_id (μ := stdGaussian E)).continuousLinearMap_comp (innerSL ℝ (b i))).integrable_sq
  rw [he,integral_finsetSum _ (fun i _ => hi i)]
  have hv (i : Fin (Module.finrank ℝ E)) : (∫ x : E,‖inner ℝ (b i) x‖^2 ∂stdGaussian E)=1 := by
    have hh := GaussianRotationVariance.dual_secondMoment (innerSL ℝ (b i))
    simpa only [innerSL_apply_apply,Real.norm_eq_abs,sq_abs,innerSL_apply_norm,b.norm_eq_one,one_pow] using hh
  simp_rw [hv]
  simp

 lemma memLp_norm_sq : MemLp (fun x : E => ‖x‖^2) 2 (stdGaussian E) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  have hh := (IsGaussian.memLp_id (stdGaussian E) 4 (by norm_num)).integrable_norm_pow'
  simpa only [id_eq,ENNReal.toReal_ofNat,← pow_mul] using hh

 theorem radius_variance_le : variance (fun x : E => ‖x‖^2) (stdGaussian E)≤
      (Real.pi^2/2)*(Module.finrank ℝ E : ℝ) := by
  have hi : Integrable (fun x : E => ‖fderiv ℝ (fun y : E => ‖y‖^2) x‖^2) (stdGaussian E) := by
    have hh := (IsGaussian.memLp_two_id (μ := stdGaussian E)).integrable_norm_pow'
    convert hh.const_mul (4 : ℝ) using 1
    funext x
    rw [fderiv_norm_sq_apply,← Nat.cast_smul_eq_nsmul ℝ,norm_smul,innerSL_apply_norm]
    norm_num
    ring
  have hb := DifferentiableGaussianVariance.gaussian_variance_le_gradient
    (fun x => (hasStrictFDerivAt_norm_sq x).hasFDerivAt.differentiableAt) memLp_norm_sq hi
  have he : (fun x : E => ‖fderiv ℝ (fun y : E => ‖y‖^2) x‖^2)=fun x => 4*‖x‖^2 := by
    funext x
    rw [fderiv_norm_sq_apply,← Nat.cast_smul_eq_nsmul ℝ,norm_smul,innerSL_apply_norm]
    norm_num
    ring
  rw [he,integral_const_mul,integral_norm_sq] at hb
  nlinarith [hb]

 theorem small_radius_probability_le (hd : 0<Module.finrank ℝ E) :
    (stdGaussian E).real {x : E | ‖x‖^2<(Module.finrank ℝ E : ℝ)/2}≤
      2*Real.pi^2/(Module.finrank ℝ E : ℝ) := by
  let d := (Module.finrank ℝ E : ℝ)
  have hd' : 0<d := Nat.cast_pos.mpr hd
  have hi := (memLp_norm_sq (E := E)).sub (memLp_const d) |>.integrable_sq
  have hMarkov := mul_meas_ge_le_integral_of_nonneg
    (.of_forall (fun x : E => sq_nonneg (‖x‖^2-d))) hi (d^2/4)
  have hsub : {x : E | ‖x‖^2<d/2}⊆{x : E | d^2/4≤(‖x‖^2-d)^2} := by
    intro x hx
    have hx' : ‖x‖^2<d/2 := hx
    have hh : d/2≤d-‖x‖^2 := by linarith
    have hh2 := pow_le_pow_left₀ (show 0≤d/2 by positivity) hh 2
    change d^2/4≤(‖x‖^2-d)^2
    calc
      _ = (d/2)^2 := by ring
      _ ≤ (d-‖x‖^2)^2 := hh2
      _ = _ := by ring
  have hv : (∫ x : E,(‖x‖^2-d)^2 ∂stdGaussian E)=variance (fun x : E => ‖x‖^2) (stdGaussian E) := by
    rw [variance_eq_integral (by fun_prop),integral_norm_sq]
  rw [hv] at hMarkov
  have hm := mul_le_mul_of_nonneg_left (measureReal_mono (μ := stdGaussian E) hsub) (show 0≤d^2/4 by positivity)
  have htot := (hm.trans hMarkov).trans (radius_variance_le (E := E))
  change (d^2/4)*(stdGaussian E).real {x : E | ‖x‖^2<d/2}≤(Real.pi^2/2)*d at htot
  rw [mul_comm] at htot
  have hdiv := (le_div_iff₀ (show 0<d^2/4 by positivity)).mpr htot
  refine hdiv.trans_eq ?_
  field_simp
  ring

end SphericalAging.GaussianRadiusVariance
