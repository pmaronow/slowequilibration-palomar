module
public import FourPapersCommon.FiniteStateCascadeGrowth
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

/-! Differentiation of the genuine finite-state Gaussian logarithmic step.
The generic input assumptions concern the previous potential; the normalized
step differential is derived by dominated differentiation, including zero mass. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ContDiff
namespace FourPapersCommon
open OverlapPaper
set_option maxHeartbeats 1200000
variable {S I : Type*} [Fintype S] [Fintype I]

def finiteStateGaussianDifferential (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (H : FiniteStateField S) : FiniteStateField S →L[ℝ] ℝ :=
  (∫ z, Real.exp (a*F (H+L z)) ∂stdGaussian (FiniteStateGaussianInput I))⁻¹ •
    (∫ z, Real.exp (a*F (H+L z)) • fderiv ℝ F (H+L z)
      ∂stdGaussian (FiniteStateGaussianInput I))

private theorem lipschitz_input (F : FiniteStateField S → ℝ)
    (hF : ContDiff ℝ 1 F) (C : ℝ≥0) (hC : ∀ H, ‖fderiv ℝ F H‖ ≤ C) :
    LipschitzWith C F := by
  apply lipschitzWith_of_nnnorm_fderiv_le (hF.differentiable (by norm_num))
  intro H
  exact NNReal.coe_le_coe.mp (hC H)

private theorem hasFDerivAt_step_exp_integral (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (hF : ContDiff ℝ 1 F)
    (C : ℝ≥0) (hC : ∀ H, ‖fderiv ℝ F H‖ ≤ C) (H : FiniteStateField S) :
    HasFDerivAt (fun H' => ∫ z, Real.exp (a*F (H'+L z)) ∂stdGaussian (FiniteStateGaussianInput I))
      (∫ z, (a*Real.exp (a*F (H+L z))) • fderiv ℝ F (H+L z)
        ∂stdGaussian (FiniteStateGaussianInput I)) H := by
  have hLip := lipschitz_input F hF C hC
  let g : FiniteStateField S → FiniteStateGaussianInput I → ℝ :=
    fun H' z => Real.exp (a*F (H'+L z))
  let D : FiniteStateField S → FiniteStateGaussianInput I → FiniteStateField S →L[ℝ] ℝ :=
    fun H' z => (a*Real.exp (a*F (H'+L z))) • fderiv ℝ F (H'+L z)
  let bound : FiniteStateGaussianInput I → ℝ :=
    fun z => (|a| *C*Real.exp (|a| *C))*Real.exp (a*F (H+L z))
  have hDf : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  have hgc (H' : FiniteStateField S) : Continuous (fun z : FiniteStateGaussianInput I => Real.exp (a*F (H'+L z))) :=
    Real.continuous_exp.comp ((hF.continuous.comp (continuous_const.add L.continuous)).const_mul a)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := g) (F' := D) (bound := bound) (Metric.ball_mem_nhds H zero_lt_one)
  · exact .of_forall fun H' => (hgc H').aestronglyMeasurable
  · exact integrable_exp_finiteStateGaussian_lipschitz F hLip L H a
  · exact ((hgc H).const_mul a |>.smul
      (hDf.comp (continuous_const.add L.continuous))).aestronglyMeasurable
  · exact .of_forall fun z H' hH' => by
      have hn : ‖H'-H‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hH'
      have hd := hLip.norm_sub_le (H'+L z) (H+L z)
      simp only [add_sub_add_right_eq_sub, Real.norm_eq_abs] at hd
      have ha : a*(F (H'+L z)-F (H+L z)) ≤ |a| *C := by
        have he := le_abs_self (a*(F (H'+L z)-F (H+L z)))
        rw [abs_mul] at he
        have hh := mul_le_mul_of_nonneg_left hd (abs_nonneg a)
        have hh' := mul_le_mul_of_nonneg_left hn.le (mul_nonneg (abs_nonneg a) C.2)
        calc
          _ ≤ |a| * |F (H'+L z)-F (H+L z)| := he
          _ ≤ |a| *(C*‖H'-H‖) := hh
          _ = (|a| *C)*‖H'-H‖ := by ring
          _ ≤ (|a| *C)*1 := mul_le_mul_of_nonneg_left hn.le (by positivity)
          _ = _ := mul_one _
      have he : Real.exp (a*F (H'+L z)) ≤ Real.exp (|a| *C)*Real.exp (a*F (H+L z)) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      change ‖(a*Real.exp (a*F (H'+L z))) • fderiv ℝ F (H'+L z)‖ ≤ _
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have hb := mul_le_mul he (hC (H'+L z)) (norm_nonneg _) (by positivity)
      have hba := mul_le_mul_of_nonneg_left hb (abs_nonneg a)
      dsimp only [bound]
      convert hba using 1 <;> ring
  · exact (integrable_exp_finiteStateGaussian_lipschitz F hLip L H a).const_mul _
  · exact .of_forall fun z H' _ => by
      have hshift : HasFDerivAt (fun K => F (K+L z)) (fderiv ℝ F (H'+L z)) H' := by
        convert (hF.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp H'
          ((hasFDerivAt_id H').add_const (L z)) using 1
        · rfl
        · ext K; rfl
      have hbase := (hshift.const_mul a).exp
      convert hbase using 1
      ext K
      simp only [D, smul_apply, smul_eq_mul]
      ring

theorem hasFDerivAt_finiteStateGaussianStep (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (hF : ContDiff ℝ 1 F)
    (C : ℝ≥0) (hC : ∀ H, ‖fderiv ℝ F H‖ ≤ C) (H : FiniteStateField S) :
    HasFDerivAt (finiteStateGaussianStep a L F) (finiteStateGaussianDifferential a L F H) H := by
  have hLip := lipschitz_input F hF C hC
  by_cases ha : a = 0
  · subst a
    have hd : HasFDerivAt (fun H' => ∫ z, F (H'+L z) ∂stdGaussian (FiniteStateGaussianInput I))
        (∫ z, fderiv ℝ F (H+L z) ∂stdGaussian (FiniteStateGaussianInput I)) H := by
      apply hasFDerivAt_integral_of_dominated_of_fderiv_le
        (F := fun H' z => F (H'+L z)) (F' := fun H' z => fderiv ℝ F (H'+L z))
        (bound := fun _ => (C : ℝ)) (Metric.ball_mem_nhds H zero_lt_one)
      · exact .of_forall fun H' => (hF.continuous.comp (by fun_prop)).aestronglyMeasurable
      · exact integrable_finiteStateGaussian_lipschitz F hLip L H
      · exact ((hF.continuous_fderiv (by norm_num)).comp (by fun_prop)).aestronglyMeasurable
      · exact .of_forall fun _ H' _ => hC _
      · exact integrable_const _
      · exact .of_forall fun z H' _ => by
          convert (hF.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp H'
            ((hasFDerivAt_id H').add_const (L z)) using 1
          · rfl
          · ext K; rfl
    convert hd using 1
    · funext H'
      simp [finiteStateGaussianStep, sourceLogAverage]
    · simp [finiteStateGaussianDifferential]
  · have he := integrable_exp_finiteStateGaussian_lipschitz F hLip L H a
    have hp : 0 < ∫ z, Real.exp (a*F (H+L z)) ∂stdGaussian (FiniteStateGaussianInput I) :=
      integral_exp_pos he
    have hd := ((hasFDerivAt_step_exp_integral a L F hF C hC H).log hp.ne').const_mul a⁻¹
    convert hd using 1
    · funext H'
      simp only [finiteStateGaussianStep, sourceLogAverage, ha, ite_false, div_eq_mul_inv]
      ring
    · rw [finiteStateGaussianDifferential]
      have hnum : (∫ z, (a*Real.exp (a*F (H+L z))) • fderiv ℝ F (H+L z)
          ∂stdGaussian (FiniteStateGaussianInput I)) =
          a • ∫ z, Real.exp (a*F (H+L z)) • fderiv ℝ F (H+L z)
            ∂stdGaussian (FiniteStateGaussianInput I) := by
        rw [← integral_smul]
        congr 1
        funext z
        rw [smul_smul]
      rw [hnum]
      ext K
      simp only [smul_apply, smul_eq_mul]
      field_simp

end FourPapersCommon
