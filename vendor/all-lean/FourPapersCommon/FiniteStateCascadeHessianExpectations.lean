module
public import FourPapersCommon.FiniteStateCascadeExpectations
public import FourPapersCommon.GenericFiniteStateCascadeBounds
public import Mathlib.Analysis.Normed.Group.Continuity

@[expose] public section

/-! The derived Gaussian-step Hessian as conditional first/second moments
under the actual normalized transition, including the zero-mass case. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
variable {S I : Type*} [Fintype S] [Fintype I]

theorem integral_finiteStateGaussianStepLaw {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (a : ℝ) (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (hF : Measurable F)
    (G : FiniteStateField S → E) (hG : StronglyMeasurable G) (H : FiniteStateField S) :
    (∫ y, G y ∂finiteStateGaussianStepLaw a L F H) =
      (∫ z, Real.exp (a*F (H+L z)) ∂stdGaussian (FiniteStateGaussianInput I))⁻¹ •
        ∫ z, Real.exp (a*F (H+L z)) • G (H+L z)
          ∂stdGaussian (FiniteStateGaussianInput I) := by
  rw [finiteStateGaussianStepLaw_eq_map_tilted a L F hF H,
    integral_map (by fun_prop : Measurable (fun z => H+L z)).aemeasurable
      hG.aestronglyMeasurable, integral_tilted, ← integral_smul]
  congr 1
  funext z
  simp only [smul_smul, div_eq_mul_inv, mul_comm]

set_option backward.isDefEq.respectTransparency false in
theorem finiteStateGaussianHessian_apply_eq_integral (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (hF : ContDiff ℝ 2 F)
    (C B : NNReal) (hC : ∀ y, ‖fderiv ℝ F y‖ ≤ C)
    (hB : ∀ y, ‖fderiv ℝ (fderiv ℝ F) y‖ ≤ B)
    (H K M : FiniteStateField S) :
    finiteStateGaussianHessian a L F H K M =
    (∫ y, (fderiv ℝ (fderiv ℝ F) y K M +
        a * fderiv ℝ F y K * fderiv ℝ F y M) ∂finiteStateGaussianStepLaw a L F H) -
        a * finiteStateGaussianDifferential a L F H K *
          finiteStateGaussianDifferential a L F H M := by
  let G : FiniteStateField S →
      (FiniteStateField S →L[ℝ] FiniteStateField S →L[ℝ] ℝ) := fun y => fderiv ℝ (fderiv ℝ F) y +
    a • (fderiv ℝ F y).smulRight (fderiv ℝ F y)
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hD : ContDiff ℝ 1 (fderiv ℝ F) := by
    exact (contDiff_succ_iff_fderiv.mp (show ContDiff ℝ ((1 : ℕ∞ω)+1) F from
      by convert hF using 1; norm_num)).2.2
  have hdyad : Continuous (fun y => (fderiv ℝ F y).smulRight (fderiv ℝ F y)) :=
    (ContinuousLinearMap.smulRightL ℝ (FiniteStateField S)
      (FiniteStateField S →L[ℝ] ℝ)).continuous₂.comp
        (hD.continuous.prodMk hD.continuous)
  have hG := (hD.continuous_fderiv (by norm_num)).add (hdyad.const_smul a)
  have hLip : LipschitzWith C F := lipschitzWith_of_nnnorm_fderiv_le hF1.differentiable_one
    (fun y => NNReal.coe_le_coe.mp (hC y))
  haveI := isProbabilityMeasure_finiteStateGaussianStepLaw a L F hF1.continuous.measurable H
    (integrable_exp_finiteStateGaussian_lipschitz F hLip L H a)
  have hb (y : FiniteStateField S) : ‖G y‖ ≤ B+|a| *C^2 := by
    apply (ContinuousLinearMap.opNorm_add_le _ _).trans
    have hs := ContinuousLinearMap.opNorm_smul_le a
      ((fderiv ℝ F y).smulRight (fderiv ℝ F y))
    simp only [Real.norm_eq_abs, ContinuousLinearMap.norm_smulRight_apply] at hs
    have hp := mul_le_mul (hC y) (hC y) (norm_nonneg _) C.2
    have ha := mul_le_mul_of_nonneg_left hp (abs_nonneg a)
    nlinarith [hB y, hs]
  let W := fun z : FiniteStateGaussianInput I => Real.exp (a*F (H+L z)) • G (H+L z)
  have hshift := (continuous_const : Continuous (fun _ : FiniteStateGaussianInput I => H)).add L.continuous
  have hw := ((Real.continuous_exp.comp
    ((hF.continuous.comp hshift).const_mul a)).smul (hG.comp hshift))
  have hi := ((integrable_exp_finiteStateGaussian_lipschitz F hLip L H a).const_mul
    (B+|a| *C^2 : ℝ)).mono' (f := W) hw.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => by
        apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        calc
          _ ≤ Real.exp (a*F (H+L z))*(B+|a| *C^2) :=
            mul_le_mul_of_nonneg_left (hb _) (Real.exp_pos _).le
          _ = _ := mul_comm _ _))
  have hp : (fun y => G y K M) = (fun y => fderiv ℝ (fderiv ℝ F) y K M +
      a * fderiv ℝ F y K * fderiv ℝ F y M) := by
    funext y
    simp only [G, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul]
    ring
  have hscalar := integral_finiteStateGaussianStepLaw a L F hF1.continuous.measurable
    (fun y => G y K M) ((hG.clm_apply continuous_const).clm_apply continuous_const).stronglyMeasurable H
  have hiK : Integrable (fun z : FiniteStateGaussianInput I => W z K)
      (stdGaussian (FiniteStateGaussianInput I)) := by
    exact (hi.norm.const_mul ‖K‖).mono'
      (hw.clm_apply continuous_const).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => by
        simpa only [mul_comm] using (W z).le_opNorm K))
  unfold finiteStateGaussianHessian
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  change _ * ((∫ z, W z ∂stdGaussian (FiniteStateGaussianInput I)) K) M - _ = _
  rw [ContinuousLinearMap.integral_apply hi K,
    ContinuousLinearMap.integral_apply hiK M]
  simp only [W, ContinuousLinearMap.smul_apply, smul_eq_mul] at hscalar ⊢
  rw [← hscalar, hp]
  ring

end FourPapersCommon
