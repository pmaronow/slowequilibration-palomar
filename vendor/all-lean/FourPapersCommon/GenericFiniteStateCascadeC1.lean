module
public import FourPapersCommon.GenericFiniteStateCascadeCalculus

@[expose] public section

/-! Actual C1 regularity of the entire finite Gaussian cascade. Dominated
continuity of the derived normalized differential supplies the induction. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ContDiff
namespace FourPapersCommon
open OverlapPaper
set_option maxHeartbeats 1200000
variable {S I : Type*} [Fintype S] [Fintype I]

private theorem step_exp_ball_bound (a : ℝ)
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
  have hh' := mul_le_mul_of_nonneg_left hn.le (mul_nonneg (abs_nonneg a) C.2)
  have hb : a*(F (H'+L z)-F (H+L z)) ≤ |a| *C := by
    calc
      _ ≤ |a| * |F (H'+L z)-F (H+L z)| := he
      _ ≤ |a| *(C*‖H'-H‖) := hh
      _ = (|a| *C)*‖H'-H‖ := by ring
      _ ≤ (|a| *C)*1 := mul_le_mul_of_nonneg_left hn.le (by positivity)
      _ = _ := mul_one _
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

theorem continuous_finiteStateGaussianDifferential (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (hF : ContDiff ℝ 1 F)
    (C : ℝ≥0) (hC : ∀ H, ‖fderiv ℝ F H‖ ≤ C) :
    Continuous (finiteStateGaussianDifferential a L F) := by
  have hLip : LipschitzWith C F := lipschitzWith_of_nnnorm_fderiv_le hF.differentiable_one
    (fun H => NNReal.coe_le_coe.mp (hC H))
  have hDf := hF.continuous_fderiv (by norm_num)
  rw [continuous_iff_continuousAt]
  intro H
  have hden : ContinuousAt (fun H' => ∫ z, Real.exp (a*F (H'+L z))
      ∂stdGaussian (FiniteStateGaussianInput I)) H := by
    apply continuousAt_of_dominated (bound := fun z => Real.exp (|a| *C)*Real.exp (a*F (H+L z)))
    · exact .of_forall fun H' =>
        (Real.continuous_exp.comp ((hF.continuous.comp (continuous_const.add L.continuous)).const_mul a)).aestronglyMeasurable
    · filter_upwards [Metric.ball_mem_nhds H zero_lt_one] with H' hH'
      exact .of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact step_exp_ball_bound a L F hLip H H' hH' z
    · exact (integrable_exp_finiteStateGaussian_lipschitz F hLip L H a).const_mul _
    · exact .of_forall fun z =>
        (Real.continuous_exp.comp ((hF.continuous.comp (continuous_id.add continuous_const)).const_mul a)).continuousAt
  have hnum : ContinuousAt (fun H' => ∫ z,
      Real.exp (a*F (H'+L z)) • fderiv ℝ F (H'+L z)
        ∂stdGaussian (FiniteStateGaussianInput I)) H := by
    apply continuousAt_of_dominated (bound := fun z => (C*Real.exp (|a| *C))*Real.exp (a*F (H+L z)))
    · exact .of_forall fun H' =>
        ((Real.continuous_exp.comp ((hF.continuous.comp
          (continuous_const.add L.continuous)).const_mul a)).smul
            (hDf.comp (continuous_const.add L.continuous))).aestronglyMeasurable
    · filter_upwards [Metric.ball_mem_nhds H zero_lt_one] with H' hH'
      exact .of_forall fun z => by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        have hb := mul_le_mul (step_exp_ball_bound a L F hLip H H' hH' z)
          (hC (H'+L z)) (norm_nonneg _) (by positivity)
        convert hb using 1
        ring
    · exact (integrable_exp_finiteStateGaussian_lipschitz F hLip L H a).const_mul _
    · exact .of_forall fun z =>
        ((Real.continuous_exp.comp ((hF.continuous.comp
          (continuous_id.add continuous_const)).const_mul a)).smul
            (hDf.comp (continuous_id.add continuous_const))).continuousAt
  have hp := integral_exp_pos (integrable_exp_finiteStateGaussian_lipschitz F hLip L H a)
  exact (hden.inv₀ hp.ne').smul hnum

theorem contDiff_one_finiteStateGaussianStep (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (hF : ContDiff ℝ 1 F)
    (C : ℝ≥0) (hC : ∀ H, ‖fderiv ℝ F H‖ ≤ C) :
    ContDiff ℝ 1 (finiteStateGaussianStep a L F) := by
  exact contDiff_one_iff_hasFDerivAt.mpr ⟨finiteStateGaussianDifferential a L F,
    continuous_finiteStateGaussianDifferential a L F hF C hC,
    hasFDerivAt_finiteStateGaussianStep a L F hF C hC⟩

theorem contDiff_one_finiteStateGaussianCascade (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (hF : ContDiff ℝ 1 F)
    {C : ℝ≥0} (hLip : LipschitzWith C F) (j : ℕ) :
    ContDiff ℝ 1 (finiteStateGaussianCascade a L F j) := by
  induction j with
  | zero => exact hF
  | succ j ih =>
    exact contDiff_one_finiteStateGaussianStep (a j) (L j)
      (finiteStateGaussianCascade a L F j) ih C (fun _ =>
        norm_fderiv_le_of_lipschitz ℝ (finiteStateGaussianCascade_lipschitz F hLip a ha L j))

theorem contDiff_one_finiteStateGaussianTerminalCascade [Nonempty S]
    (V : S → ℝ) (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (j : ℕ) :
    ContDiff ℝ 1 (finiteStateGaussianTerminalCascade V a L j) :=
  contDiff_one_finiteStateGaussianCascade a ha L _
    ((SpinGlass.AT.contDiff_gtStateLogPartition V).of_le (by norm_num))
    (finiteStateGaussianTerminal_lipschitz V) j

theorem hasFDerivAt_finiteStateGaussianTerminalCascade_succ [Nonempty S]
    (V : S → ℝ) (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (H : FiniteStateField S) :
    HasFDerivAt (finiteStateGaussianTerminalCascade V a L (j+1))
      (finiteStateGaussianDifferential (a j) (L j)
        (finiteStateGaussianTerminalCascade V a L j) H) H :=
  hasFDerivAt_finiteStateGaussianStep (a j) (L j) _
    (contDiff_one_finiteStateGaussianTerminalCascade V a ha L j) 1
    (fun _ => norm_fderiv_le_of_lipschitz ℝ (finiteStateGaussianTerminalCascade_lipschitz V a ha L j)) H

end FourPapersCommon
