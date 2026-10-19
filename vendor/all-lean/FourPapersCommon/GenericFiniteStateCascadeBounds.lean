module
public import FourPapersCommon.GenericFiniteStateCascadeC2

@[expose] public section

/-! Quantitative Hessian bounds for the actual finite-state Gaussian cascade.
These bounds discharge the regularity premises of repeated covariance calculus. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ContDiff BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 1600000
variable {S I : Type*} [Fintype S] [Fintype I]

def finiteStateGaussianHessian (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (H : FiniteStateField S) :
    FiniteStateField S →L[ℝ] FiniteStateField S →L[ℝ] ℝ :=
  (∫ z, Real.exp (a*F (H+L z)) ∂stdGaussian (FiniteStateGaussianInput I))⁻¹ •
    finiteStateWeightedSecond a L F H -
    a • (finiteStateGaussianDifferential a L F H).smulRight
      (finiteStateGaussianDifferential a L F H)

private theorem exp_integral_eq_step (a : ℝ)
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

theorem hasFDerivAt_finiteStateGaussianDifferential (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (hF : ContDiff ℝ 2 F)
    (C B : ℝ≥0) (hC : ∀ H, ‖fderiv ℝ F H‖ ≤ C)
    (hB : ∀ H, ‖fderiv ℝ (fderiv ℝ F) H‖ ≤ B) (H : FiniteStateField S) :
    HasFDerivAt (finiteStateGaussianDifferential a L F)
      (finiteStateGaussianHessian a L F H) H := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hLip : LipschitzWith C F := lipschitzWith_of_nnnorm_fderiv_le hF1.differentiable_one
    (fun y => NNReal.coe_le_coe.mp (hC y))
  let den := fun H' => ∫ z, Real.exp (a*F (H'+L z)) ∂stdGaussian (FiniteStateGaussianInput I)
  have hp : 0 < den H := integral_exp_pos
    (integrable_exp_finiteStateGaussian_lipschitz F hLip L H a)
  have heq : den = fun H' => Real.exp (a*finiteStateGaussianStep a L F H') :=
    funext (exp_integral_eq_step a L F hLip)
  have hden : HasFDerivAt den ((a*den H) • finiteStateGaussianDifferential a L F H) H := by
    have hd := ((hasFDerivAt_finiteStateGaussianStep a L F hF1 C hC H).const_mul a).exp
    rw [heq]
    convert hd using 1
    ext K
    simp only [smul_apply, smul_eq_mul]
    ring
  have hi : HasFDerivAt (fun H' => (den H')⁻¹)
      (-(den H ^ 2)⁻¹ • ((a*den H) • finiteStateGaussianDifferential a L F H)) H := by
    have hd := (hasFDerivAt_inv hp.ne').comp H hden
    have he : (ContinuousLinearMap.toSpanSingleton ℝ (-(den H ^ 2)⁻¹)).comp
        ((a*den H) • finiteStateGaussianDifferential a L F H) =
        -(den H ^ 2)⁻¹ • ((a*den H) • finiteStateGaussianDifferential a L F H) := by
      ext K
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
        smul_apply, smul_eq_mul]
      ring
    rw [he] at hd
    exact hd
  have hw := hasFDerivAt_finiteStateWeightedFirst a L F hF C B hC hB H
  have hd := hi.smul hw
  convert hd using 1
  · rfl
  · ext K J
    simp only [finiteStateGaussianHessian, finiteStateGaussianDifferential,
      finiteStateWeightedFirst, den, smul_apply, sub_apply, add_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul]
    have hn : (∫ z, Real.exp (a*F (H+L z)) ∂stdGaussian (FiniteStateGaussianInput I)) ≠ 0 := hp.ne'
    field_simp [hn]
    ring

private theorem second_integrand_norm_bound (a : ℝ) (F : FiniteStateField S → ℝ)
    (C B : ℝ≥0) (hC : ∀ H, ‖fderiv ℝ F H‖ ≤ C)
    (hB : ∀ H, ‖fderiv ℝ (fderiv ℝ F) H‖ ≤ B) (y : FiniteStateField S) :
    ‖fderiv ℝ (fderiv ℝ F) y + a • (fderiv ℝ F y).smulRight (fderiv ℝ F y)‖ ≤
      B + |a| *C^2 := by
  apply (ContinuousLinearMap.opNorm_add_le _ _).trans
  have hs : ‖a • (fderiv ℝ F y).smulRight (fderiv ℝ F y)‖ ≤
      |a| * (‖fderiv ℝ F y‖ * ‖fderiv ℝ F y‖) := by
    convert ContinuousLinearMap.opNorm_smul_le a
      ((fderiv ℝ F y).smulRight (fderiv ℝ F y)) using 1
    simp only [Real.norm_eq_abs, ContinuousLinearMap.norm_smulRight_apply]
  have hp := mul_le_mul (hC y) (hC y) (norm_nonneg _) C.2
  have ha := mul_le_mul_of_nonneg_left hp (abs_nonneg a)
  nlinarith [hB y, hs]

theorem norm_finiteStateWeightedSecond_le (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (hF : ContDiff ℝ 2 F)
    (C B : ℝ≥0) (hC : ∀ H, ‖fderiv ℝ F H‖ ≤ C)
    (hB : ∀ H, ‖fderiv ℝ (fderiv ℝ F) H‖ ≤ B) (H : FiniteStateField S) :
    ‖finiteStateWeightedSecond a L F H‖ ≤
      (B+|a| *C^2)*(∫ z, Real.exp (a*F (H+L z)) ∂stdGaussian (FiniteStateGaussianInput I)) := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hLip : LipschitzWith C F := lipschitzWith_of_nnnorm_fderiv_le hF1.differentiable_one
    (fun y => NNReal.coe_le_coe.mp (hC y))
  have hi := (integrable_exp_finiteStateGaussian_lipschitz F hLip L H a).const_mul
    ((B : ℝ)+|a| *C^2)
  have hb : ∀ᵐ z ∂stdGaussian (FiniteStateGaussianInput I),
      ‖Real.exp (a*F (H+L z)) • (fderiv ℝ (fderiv ℝ F) (H+L z) +
        a • (fderiv ℝ F (H+L z)).smulRight (fderiv ℝ F (H+L z)))‖ ≤
          (B+|a| *C^2)*Real.exp (a*F (H+L z)) := .of_forall fun z => by
    apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (a*F (H+L z))*(B+|a| *C^2) :=
        mul_le_mul_of_nonneg_left (second_integrand_norm_bound a F C B hC hB _) (Real.exp_pos _).le
      _ = _ := mul_comm _ _
  simpa only [finiteStateWeightedSecond, integral_const_mul] using
    norm_integral_le_of_norm_le hi hb

theorem norm_finiteStateGaussianHessian_le (a : ℝ) (ha : 0 ≤ a)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (hF : ContDiff ℝ 2 F)
    (C B : ℝ≥0) (hC : ∀ H, ‖fderiv ℝ F H‖ ≤ C)
    (hB : ∀ H, ‖fderiv ℝ (fderiv ℝ F) H‖ ≤ B) (H : FiniteStateField S) :
    ‖finiteStateGaussianHessian a L F H‖ ≤ B+2*a*C^2 := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hLip : LipschitzWith C F := lipschitzWith_of_nnnorm_fderiv_le hF1.differentiable_one
    (fun y => NNReal.coe_le_coe.mp (hC y))
  let d := ∫ z, Real.exp (a*F (H+L z)) ∂stdGaussian (FiniteStateGaussianInput I)
  have hd : 0 < d := integral_exp_pos (integrable_exp_finiteStateGaussian_lipschitz F hLip L H a)
  have hn := norm_finiteStateWeightedSecond_le a L F hF C B hC hB H
  have hc : ‖finiteStateGaussianDifferential a L F H‖ ≤ C := by
    rw [← (hasFDerivAt_finiteStateGaussianStep a L F hF1 C hC H).fderiv]
    exact norm_fderiv_le_of_lipschitz ℝ (finiteStateGaussianStep_lipschitz F hLip a ha L)
  have hfirst : ‖d⁻¹ • finiteStateWeightedSecond a L F H‖ ≤ B+a*C^2 := by
    apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
    have h := mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hd.le)
    calc
      _ ≤ d⁻¹*((B+a*C^2)*d) := by simpa only [abs_of_nonneg ha] using h
      _ = _ := by field_simp
  have hsecond : ‖a • (finiteStateGaussianDifferential a L F H).smulRight
      (finiteStateGaussianDifferential a L F H)‖ ≤ a*C^2 := by
    apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
    rw [Real.norm_eq_abs, abs_of_nonneg ha, ContinuousLinearMap.norm_smulRight_apply]
    have hp := mul_le_mul hc hc (norm_nonneg _) C.2
    nlinarith [mul_le_mul_of_nonneg_left hp ha]
  calc
    _ ≤ ‖d⁻¹ • finiteStateWeightedSecond a L F H‖ +
        ‖a • (finiteStateGaussianDifferential a L F H).smulRight
          (finiteStateGaussianDifferential a L F H)‖ :=
      by
        apply ContinuousLinearMap.opNorm_le_bound _
          (add_nonneg (ContinuousLinearMap.opNorm_nonneg _) (ContinuousLinearMap.opNorm_nonneg _))
        intro K
        change ‖(d⁻¹ • finiteStateWeightedSecond a L F H) K -
          (a • (finiteStateGaussianDifferential a L F H).smulRight
            (finiteStateGaussianDifferential a L F H)) K‖ ≤ _
        calc
          _ ≤ ‖(d⁻¹ • finiteStateWeightedSecond a L F H) K‖ +
              ‖(a • (finiteStateGaussianDifferential a L F H).smulRight
                (finiteStateGaussianDifferential a L F H)) K‖ := norm_sub_le _ _
          _ ≤ ‖d⁻¹ • finiteStateWeightedSecond a L F H‖*‖K‖ +
              ‖a • (finiteStateGaussianDifferential a L F H).smulRight
                (finiteStateGaussianDifferential a L F H)‖*‖K‖ :=
            add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
          _ = _ := by ring
    _ ≤ (B+a*C^2)+(a*C^2) := add_le_add hfirst hsecond
    _ = _ := by ring

theorem norm_second_fderiv_finiteStateGaussianTerminal_le [Nonempty S]
    (V : S → ℝ) (H : FiniteStateField S) :
    ‖fderiv ℝ (fderiv ℝ (SpinGlass.AT.gtStateLogPartition V)) H‖ ≤ 2 := by
  classical
  have hfirst : ∀ H', ‖fderiv ℝ (SpinGlass.AT.gtStateLogPartition V) H'‖ ≤ 1 :=
    fun _ => norm_fderiv_le_of_lipschitz ℝ (finiteStateGaussianTerminal_lipschitz V)
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro K
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro J
  rw [SpinGlass.AT.second_fderiv_gtStateLogPartition_apply, Real.norm_eq_abs]
  have hK : ∀ σ : S, |K σ| ≤ ‖K‖ := fun σ => by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le K σ
  have hJ : ∀ σ : S, |J σ| ≤ ‖J‖ := fun σ => by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le J σ
  have hprod : |∑ σ : S, SpinGlass.AT.gtStateGibbs V H σ * K σ * J σ| ≤ ‖K‖*‖J‖ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ σ : S, SpinGlass.AT.gtStateGibbs V H σ * (‖K‖*‖J‖) :=
        Finset.sum_le_sum fun σ _ => by
          rw [abs_mul, abs_mul, abs_of_nonneg (SpinGlass.AT.gtStateGibbs_nonneg V H σ)]
          have hp := mul_le_mul (hK σ) (hJ σ) (abs_nonneg _) (norm_nonneg _)
          have h := mul_le_mul_of_nonneg_left hp (SpinGlass.AT.gtStateGibbs_nonneg V H σ)
          nlinarith
      _ = _ := by rw [← Finset.sum_mul, SpinGlass.AT.sum_gtStateGibbs]; simp
  have hmean (A : FiniteStateField S) :
      |∑ σ : S, SpinGlass.AT.gtStateGibbs V H σ * A σ| ≤ ‖A‖ := by
    rw [← SpinGlass.AT.fderiv_gtStateLogPartition_apply]
    have h := (fderiv ℝ (SpinGlass.AT.gtStateLogPartition V) H).le_opNorm A
    rw [Real.norm_eq_abs] at h
    exact h.trans (by simpa using mul_le_mul_of_nonneg_right (hfirst H) (norm_nonneg A))
  apply (abs_sub _ _).trans
  rw [abs_mul]
  have hm := mul_le_mul (hmean K) (hmean J) (abs_nonneg _) (norm_nonneg _)
  nlinarith

def finiteStateCascadeHessianBound (a : ℕ → ℝ) : ℕ → ℝ≥0
  | 0 => 2
  | j+1 => finiteStateCascadeHessianBound a j+2*Real.toNNReal (a j)

@[simp] theorem finiteStateCascadeHessianBound_zero (a : ℕ → ℝ) :
    finiteStateCascadeHessianBound a 0 = 2 := rfl

theorem finiteStateCascadeHessianBound_succ (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (j : ℕ) :
    (finiteStateCascadeHessianBound a (j+1) : ℝ) = finiteStateCascadeHessianBound a j+2*a j := by
  simp [finiteStateCascadeHessianBound, Real.toNNReal_of_nonneg (ha j)]

theorem finiteStateGaussianTerminalCascade_C2_bounds [Nonempty S]
    (V : S → ℝ) (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (j : ℕ) :
    ContDiff ℝ 2 (finiteStateGaussianTerminalCascade V a L j) ∧
      ∀ H, ‖fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) H‖ ≤
        finiteStateCascadeHessianBound a j := by
  induction j with
  | zero =>
    refine ⟨(SpinGlass.AT.contDiff_gtStateLogPartition V).of_le (by norm_num), ?_⟩
    simpa only [finiteStateGaussianTerminalCascade, finiteStateGaussianCascade,
      finiteStateCascadeHessianBound_zero, NNReal.coe_ofNat] using
        norm_second_fderiv_finiteStateGaussianTerminal_le V
  | succ j ih =>
    have hgrad : ∀ H, ‖fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) H‖ ≤ (1 : ℝ≥0) :=
      fun _ => norm_fderiv_le_of_lipschitz ℝ
        (finiteStateGaussianTerminalCascade_lipschitz V a ha L j)
    refine ⟨contDiff_two_finiteStateGaussianStep (a j) (L j) _ ih.1 1
      (finiteStateCascadeHessianBound a j) hgrad ih.2, ?_⟩
    intro H
    have hEq : fderiv ℝ (finiteStateGaussianTerminalCascade V a L (j+1)) =
        finiteStateGaussianDifferential (a j) (L j) (finiteStateGaussianTerminalCascade V a L j) :=
      funext fun H' => (hasFDerivAt_finiteStateGaussianTerminalCascade_succ V a ha L j H').fderiv
    rw [hEq, (hasFDerivAt_finiteStateGaussianDifferential (a j) (L j) _ ih.1 1
      (finiteStateCascadeHessianBound a j) hgrad ih.2 H).fderiv,
      finiteStateCascadeHessianBound_succ a ha j]
    simpa using norm_finiteStateGaussianHessian_le (a j) (ha j) (L j) _ ih.1 1
      (finiteStateCascadeHessianBound a j) hgrad ih.2 H

theorem contDiff_two_finiteStateGaussianTerminalCascade [Nonempty S]
    (V : S → ℝ) (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (j : ℕ) :
    ContDiff ℝ 2 (finiteStateGaussianTerminalCascade V a L j) :=
  (finiteStateGaussianTerminalCascade_C2_bounds V a ha L j).1

end FourPapersCommon
