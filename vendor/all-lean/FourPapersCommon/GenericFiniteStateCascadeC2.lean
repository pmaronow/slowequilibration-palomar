module
public import FourPapersCommon.GenericFiniteStateCascadeC1

@[expose] public section

/-! Second-order differentiation of the Gaussian cascade step. The weighted
first derivative has an actual Fréchet derivative obtained under the Gaussian
integral. This is the Hessian substrate for covariance interpolation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1600000
variable {S I : Type*} [Fintype S] [Fintype I]

def finiteStateWeightedFirst (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (H : FiniteStateField S) : FiniteStateField S →L[ℝ] ℝ :=
  ∫ z, Real.exp (a*F (H+L z)) • fderiv ℝ F (H+L z) ∂stdGaussian (FiniteStateGaussianInput I)

def finiteStateWeightedSecond (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (H : FiniteStateField S) :
    FiniteStateField S →L[ℝ] FiniteStateField S →L[ℝ] ℝ :=
  ∫ z, Real.exp (a*F (H+L z)) •
    (fderiv ℝ (fderiv ℝ F) (H+L z) + a •
      (fderiv ℝ F (H+L z)).smulRight (fderiv ℝ F (H+L z)))
        ∂stdGaussian (FiniteStateGaussianInput I)

private theorem exp_local_bound (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) {C : ℝ≥0} (hF : LipschitzWith C F)
    (H H' : FiniteStateField S) (hH' : H' ∈ Metric.ball H 1) (z : FiniteStateGaussianInput I) :
    Real.exp (a*F (H'+L z)) ≤ Real.exp (|a| *C)*Real.exp (a*F (H+L z)) := by
  have hn : ‖H'-H‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hH'
  have hd := hF.norm_sub_le (H'+L z) (H+L z)
  simp only [add_sub_add_right_eq_sub, Real.norm_eq_abs] at hd
  have he := le_abs_self (a*(F (H'+L z)-F (H+L z)))
  rw [abs_mul] at he
  have hh := mul_le_mul_of_nonneg_left hd (abs_nonneg a)
  have hb : a*(F (H'+L z)-F (H+L z)) ≤ |a| *C := by
    calc
      _ ≤ |a| * |F (H'+L z)-F (H+L z)| := he
      _ ≤ |a| *(C*‖H'-H‖) := hh
      _ = (|a| *C)*‖H'-H‖ := by ring
      _ ≤ (|a| *C)*1 := mul_le_mul_of_nonneg_left hn.le (by positivity)
      _ = _ := mul_one _
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

private theorem contDiff_fderiv_of_two (F : FiniteStateField S → ℝ)
    (hF : ContDiff ℝ 2 F) : ContDiff ℝ 1 (fderiv ℝ F) := by
  have hF' : ContDiff ℝ ((1 : ℕ∞ω) + 1) F := by
    convert hF using 1
    norm_num
  exact (contDiff_succ_iff_fderiv.mp hF').2.2

private theorem bilinear_norm_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : E →L[ℝ] E →L[ℝ] ℝ) : ‖A+B‖ ≤ ‖A‖+‖B‖ := ContinuousLinearMap.opNorm_add_le _ _

private theorem bilinear_norm_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E →L[ℝ] ℝ) : 0 ≤ ‖A‖ := A.opNorm_nonneg

private theorem weighted_second_integrand_bound (a : ℝ) (F : FiniteStateField S → ℝ)
    (C B : ℝ≥0) (hC : ∀ H, ‖fderiv ℝ F H‖ ≤ C)
    (hB : ∀ H, ‖fderiv ℝ (fderiv ℝ F) H‖ ≤ B) (y : FiniteStateField S) :
    ‖fderiv ℝ (fderiv ℝ F) y + a • (fderiv ℝ F y).smulRight (fderiv ℝ F y)‖ ≤
      B + |a| *C^2 := by
  apply (bilinear_norm_add _ _).trans
  have hs : ‖a • (fderiv ℝ F y).smulRight (fderiv ℝ F y)‖ ≤
      |a| * (‖fderiv ℝ F y‖ * ‖fderiv ℝ F y‖) := by
    convert ContinuousLinearMap.opNorm_smul_le a
      ((fderiv ℝ F y).smulRight (fderiv ℝ F y)) using 1
    simp only [Real.norm_eq_abs, ContinuousLinearMap.norm_smulRight_apply]
  have hp := mul_le_mul (hC y) (hC y) (norm_nonneg _) C.2
  have ha := mul_le_mul_of_nonneg_left hp (abs_nonneg a)
  nlinarith [hB y, hs]

theorem hasFDerivAt_finiteStateWeightedFirst (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (hF : ContDiff ℝ 2 F)
    (C B : ℝ≥0) (hC : ∀ H, ‖fderiv ℝ F H‖ ≤ C)
    (hB : ∀ H, ‖fderiv ℝ (fderiv ℝ F) H‖ ≤ B) (H : FiniteStateField S) :
    HasFDerivAt (finiteStateWeightedFirst a L F) (finiteStateWeightedSecond a L F H) H := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hD1 := contDiff_fderiv_of_two F hF
  have hLip : LipschitzWith C F := lipschitzWith_of_nnnorm_fderiv_le hF1.differentiable_one
    (fun y => NNReal.coe_le_coe.mp (hC y))
  let g : FiniteStateField S → FiniteStateGaussianInput I → FiniteStateField S →L[ℝ] ℝ :=
    fun H' z => Real.exp (a*F (H'+L z)) • fderiv ℝ F (H'+L z)
  let D : FiniteStateField S → FiniteStateGaussianInput I →
      FiniteStateField S →L[ℝ] FiniteStateField S →L[ℝ] ℝ := fun H' z =>
    Real.exp (a*F (H'+L z)) • (fderiv ℝ (fderiv ℝ F) (H'+L z) +
      a • (fderiv ℝ F (H'+L z)).smulRight (fderiv ℝ F (H'+L z)))
  let bound := fun z : FiniteStateGaussianInput I =>
    ((B+|a| *C^2)*Real.exp (|a| *C))*Real.exp (a*F (H+L z))
  have hdcont := hD1.continuous
  have hddcont := hD1.continuous_fderiv (by norm_num)
  have hdyad : Continuous (fun y => (fderiv ℝ F y).smulRight (fderiv ℝ F y)) :=
    (ContinuousLinearMap.smulRightL ℝ (FiniteStateField S) (FiniteStateField S →L[ℝ] ℝ)).continuous₂.comp
      (hdcont.prodMk hdcont)
  have hA := hddcont.add (hdyad.const_smul a)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (F := g) (F' := D)
    (bound := bound) (Metric.ball_mem_nhds H zero_lt_one)
  · exact .of_forall fun H' =>
      ((Real.continuous_exp.comp ((hF.continuous.comp
        (continuous_const.add L.continuous)).const_mul a)).smul
          (hdcont.comp (continuous_const.add L.continuous))).aestronglyMeasurable
  · apply ((integrable_exp_finiteStateGaussian_lipschitz F hLip L H a).const_mul (C : ℝ)).mono'
      (((Real.continuous_exp.comp ((hF.continuous.comp
        (continuous_const.add L.continuous)).const_mul a)).smul
          (hdcont.comp (continuous_const.add L.continuous))).aestronglyMeasurable)
    exact .of_forall fun z => by
      change ‖Real.exp (a*F (H+L z)) • fderiv ℝ F (H+L z)‖ ≤ _
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      calc
        _ ≤ Real.exp (a*F (H+L z)) * C :=
          mul_le_mul_of_nonneg_left (hC (H+L z)) (Real.exp_pos _).le
        _ = _ := mul_comm _ _
  · exact ((Real.continuous_exp.comp ((hF.continuous.comp
        (continuous_const.add L.continuous)).const_mul a)).smul
          (hA.comp (continuous_const.add L.continuous))).aestronglyMeasurable
  · exact .of_forall fun z H' hH' => by
      rw [show D H' z = _ from rfl, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have hb := mul_le_mul (exp_local_bound a L F hLip H H' hH' z)
        (weighted_second_integrand_bound a F C B hC hB (H'+L z)) (bilinear_norm_nonneg _) (by positivity)
      dsimp only [bound]
      convert hb using 1
      ring
  · exact (integrable_exp_finiteStateGaussian_lipschitz F hLip L H a).const_mul _
  · exact .of_forall fun z H' _ => by
      have hf : HasFDerivAt (fun y => F (y+L z)) (fderiv ℝ F (H'+L z)) H' := by
        convert hF1.differentiable_one.differentiableAt.hasFDerivAt.comp H'
          ((hasFDerivAt_id H').add_const (L z)) using 1
        · rfl
        · ext K; rfl
      have hd : HasFDerivAt (fun y => fderiv ℝ F (y+L z))
          (fderiv ℝ (fderiv ℝ F) (H'+L z)) H' := by
        convert hD1.differentiable_one.differentiableAt.hasFDerivAt.comp H'
          ((hasFDerivAt_id H').add_const (L z)) using 1
        · rfl
        · ext K; rfl
      have hb := ((hf.const_mul a).exp).smul hd
      convert hb using 1
      ext K J
      simp only [D, smul_apply, add_apply, ContinuousLinearMap.smulRight_apply,
        smul_eq_mul]
      ring

theorem continuous_finiteStateWeightedSecond (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (hF : ContDiff ℝ 2 F)
    (C B : ℝ≥0) (hC : ∀ H, ‖fderiv ℝ F H‖ ≤ C)
    (hB : ∀ H, ‖fderiv ℝ (fderiv ℝ F) H‖ ≤ B) :
    Continuous (finiteStateWeightedSecond a L F) := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hD1 := contDiff_fderiv_of_two F hF
  have hLip : LipschitzWith C F := lipschitzWith_of_nnnorm_fderiv_le hF1.differentiable_one
    (fun y => NNReal.coe_le_coe.mp (hC y))
  have hdcont := hD1.continuous
  have hddcont := hD1.continuous_fderiv (by norm_num)
  have hdyad : Continuous (fun y => (fderiv ℝ F y).smulRight (fderiv ℝ F y)) :=
    (ContinuousLinearMap.smulRightL ℝ (FiniteStateField S) (FiniteStateField S →L[ℝ] ℝ)).continuous₂.comp
      (hdcont.prodMk hdcont)
  have hA := hddcont.add (hdyad.const_smul a)
  rw [continuous_iff_continuousAt]
  intro H
  apply continuousAt_of_dominated
    (bound := fun z => ((B+|a| *C^2)*Real.exp (|a| *C))*Real.exp (a*F (H+L z)))
  · exact .of_forall fun H' =>
      ((Real.continuous_exp.comp ((hF.continuous.comp
        (continuous_const.add L.continuous)).const_mul a)).smul
          (hA.comp (continuous_const.add L.continuous))).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds H zero_lt_one] with H' hH'
    exact .of_forall fun z => by
      change ‖Real.exp (a*F (H'+L z)) • _‖ ≤ _
      apply (ContinuousLinearMap.opNorm_smul_le (Real.exp (a*F (H'+L z))) _).trans
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have hb := mul_le_mul (exp_local_bound a L F hLip H H' hH' z)
        (weighted_second_integrand_bound a F C B hC hB (H'+L z))
        (bilinear_norm_nonneg _) (by positivity)
      convert hb using 1
      ring
  · exact (integrable_exp_finiteStateGaussian_lipschitz F hLip L H a).const_mul _
  · exact .of_forall fun z =>
      ((Real.continuous_exp.comp ((hF.continuous.comp
        (continuous_id.add continuous_const)).const_mul a)).smul
          (hA.comp (continuous_id.add continuous_const))).continuousAt

theorem contDiff_one_finiteStateWeightedFirst (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (hF : ContDiff ℝ 2 F)
    (C B : ℝ≥0) (hC : ∀ H, ‖fderiv ℝ F H‖ ≤ C)
    (hB : ∀ H, ‖fderiv ℝ (fderiv ℝ F) H‖ ≤ B) :
    ContDiff ℝ 1 (finiteStateWeightedFirst a L F) :=
  contDiff_one_iff_hasFDerivAt.mpr ⟨finiteStateWeightedSecond a L F,
    continuous_finiteStateWeightedSecond a L F hF C B hC hB,
    hasFDerivAt_finiteStateWeightedFirst a L F hF C B hC hB⟩

private theorem exp_integral_eq_exp_step (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) {C : ℝ≥0} (hLip : LipschitzWith C F)
    (H : FiniteStateField S) :
    (∫ z, Real.exp (a*F (H+L z)) ∂stdGaussian (FiniteStateGaussianInput I)) =
      Real.exp (a*finiteStateGaussianStep a L F H) := by
  by_cases ha : a = 0
  · simp [ha]
  · have hp := integral_exp_pos (integrable_exp_finiteStateGaussian_lipschitz F hLip L H a)
    simp only [finiteStateGaussianStep, OverlapPaper.sourceLogAverage, ha, ite_false]
    rw [mul_div_cancel₀ _ ha, Real.exp_log hp]

theorem contDiff_one_finiteStateGaussianDifferential (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (hF : ContDiff ℝ 2 F)
    (C B : ℝ≥0) (hC : ∀ H, ‖fderiv ℝ F H‖ ≤ C)
    (hB : ∀ H, ‖fderiv ℝ (fderiv ℝ F) H‖ ≤ B) :
    ContDiff ℝ 1 (finiteStateGaussianDifferential a L F) := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hLip : LipschitzWith C F := lipschitzWith_of_nnnorm_fderiv_le hF1.differentiable_one
    (fun y => NNReal.coe_le_coe.mp (hC y))
  have hden : ContDiff ℝ 1 (fun H => ∫ z, Real.exp (a*F (H+L z))
      ∂stdGaussian (FiniteStateGaussianInput I)) := by
    have heq : (fun H => ∫ z, Real.exp (a*F (H+L z))
        ∂stdGaussian (FiniteStateGaussianInput I)) =
        (fun H => Real.exp (a*finiteStateGaussianStep a L F H)) :=
      funext (exp_integral_eq_exp_step a L F hLip)
    rw [heq]
    exact (contDiff_const.mul (contDiff_one_finiteStateGaussianStep a L F hF1 C hC)).exp
  exact (hden.inv (fun H => (integral_exp_pos
    (integrable_exp_finiteStateGaussian_lipschitz F hLip L H a)).ne')).smul
      (contDiff_one_finiteStateWeightedFirst a L F hF C B hC hB)

theorem contDiff_two_finiteStateGaussianStep (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (hF : ContDiff ℝ 2 F)
    (C B : ℝ≥0) (hC : ∀ H, ‖fderiv ℝ F H‖ ≤ C)
    (hB : ∀ H, ‖fderiv ℝ (fderiv ℝ F) H‖ ≤ B) :
    ContDiff ℝ 2 (finiteStateGaussianStep a L F) := by
  have h : ContDiff ℝ ((1 : ℕ)+1) (finiteStateGaussianStep a L F) :=
    contDiff_succ_iff_hasFDerivAt.mpr ⟨finiteStateGaussianDifferential a L F,
      contDiff_one_finiteStateGaussianDifferential a L F hF C B hC hB,
      hasFDerivAt_finiteStateGaussianStep a L F (hF.of_le (by norm_num)) C hC⟩
  convert h using 1
  norm_num

end FourPapersCommon
