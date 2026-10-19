module
public import FourPapersCommon.FiniteStateCascadeDefinitions
public import OverlapPaper.ReplicaSourceMarkovRecursion

@[expose] public section

/-! Exponential integrability and stable Lipschitz bounds for the actual
finite-state Gaussian logarithmic recursion. These discharge analytic growth
conditions instead of treating cascade regularity as an assumption. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open OverlapPaper
namespace FourPapersCommon
set_option maxHeartbeats 800000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem integrable_exp_mul_norm_gaussian (μ : Measure E) [IsGaussian μ] (c : ℝ) :
    Integrable (fun x => Real.exp (c * ‖x‖)) μ := by
  obtain ⟨ε, hε, hi⟩ := IsGaussian.exists_integrable_exp_sq μ
  have hbound (x : E) : c * ‖x‖ ≤ ε * ‖x‖ ^ 2 + c ^ 2 / ε := by
    have hsq := sq_nonneg (ε * ‖x‖ - c)
    have he : ε * (c ^ 2 / ε) = c ^ 2 := by field_simp
    nlinarith [norm_nonneg x, sq_nonneg c, mul_pos hε hε]
  refine (hi.const_mul (Real.exp (c ^ 2 / ε))).mono' (by fun_prop) ?_
  exact .of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [hbound x])

variable {S I : Type*} [Fintype S] [Fintype I]

theorem integrable_finiteStateGaussian_lipschitz (F : FiniteStateField S → ℝ)
    {C : NNReal} (hF : LipschitzWith C F)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (H : FiniteStateField S) :
    Integrable (fun z => F (H + L z)) (stdGaussian (FiniteStateGaussianInput I)) := by
  have hb (z : FiniteStateGaussianInput I) : |F (H + L z)| ≤
      |F H| + (C : ℝ) * ‖L‖ * ‖z‖ := by
    have hd := hF.norm_sub_le (H + L z) H
    simp only [add_sub_cancel_left] at hd
    calc
      _ ≤ |F (H + L z) - F H| + |F H| := by
        have hh := abs_add_le (F (H + L z) - F H) (F H)
        simpa only [sub_add_cancel] using hh
      _ ≤ (C : ℝ) * ‖L z‖ + |F H| := by
        simp only [Real.norm_eq_abs] at hd
        linarith only [hd]
      _ ≤ _ := by have hl := L.le_opNorm z; nlinarith [NNReal.coe_nonneg C]
  have hi := (IsGaussian.integrable_id (μ := stdGaussian (FiniteStateGaussianInput I))).norm
  refine ((integrable_const |F H|).add (hi.const_mul ((C : ℝ) * ‖L‖))).mono'
    (hF.continuous.comp (by fun_prop)).aestronglyMeasurable ?_
  exact .of_forall fun z => by simpa only [Real.norm_eq_abs, Pi.add_apply, id_eq] using hb z

theorem integrable_exp_finiteStateGaussian_lipschitz (F : FiniteStateField S → ℝ)
    {C : NNReal} (hF : LipschitzWith C F)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (H : FiniteStateField S) (a : ℝ) :
    Integrable (fun z => Real.exp (a * F (H + L z)))
      (stdGaussian (FiniteStateGaussianInput I)) := by
  have hb (z : FiniteStateGaussianInput I) :
      a * F (H + L z) ≤ a * F H + (|a| * C * ‖L‖) * ‖z‖ := by
    have hd := hF.norm_sub_le (H + L z) H
    simp only [add_sub_cancel_left, Real.norm_eq_abs] at hd
    have hl := L.le_opNorm z
    have ha := le_abs_self (a * (F (H + L z) - F H))
    rw [abs_mul] at ha
    have hmul := mul_le_mul_of_nonneg_left hd (abs_nonneg a)
    have hmul' := mul_le_mul_of_nonneg_left hl (mul_nonneg (abs_nonneg a) C.coe_nonneg)
    nlinarith
  refine ((integrable_exp_mul_norm_gaussian (stdGaussian (FiniteStateGaussianInput I))
    (|a| * C * ‖L‖)).const_mul (Real.exp (a * F H))).mono' ((Real.continuous_exp.comp ((hF.continuous.comp (by fun_prop)).const_mul a)).aestronglyMeasurable) ?_
  exact .of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
      exact Real.exp_le_exp.mpr (hb z)


theorem sourceLogAverage_sub_tilted_all {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (a : ℝ) (f g : A → ℝ)
    (hfi : Integrable f μ) (hgi : Integrable g μ)
    (hfe : Integrable (fun x => Real.exp (a * f x)) μ)
    (hge : Integrable (fun x => Real.exp (a * g x)) μ) :
    sourceLogAverage μ a f - sourceLogAverage μ a g =
      sourceLogAverage (μ.tilted (fun x => a * g x)) a (fun x => f x - g x) := by
  by_cases ha : a = 0
  · subst a
    simpa [sourceLogAverage] using (integral_sub hfi hgi).symm
  · exact sourceLogAverage_sub_tilted μ a ha f g hfe hge

theorem finiteStateGaussianStep_lipschitz (F : FiniteStateField S → ℝ)
    {C : NNReal} (hF : LipschitzWith C F) (a : ℝ) (ha : 0 ≤ a)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) :
    LipschitzWith C (finiteStateGaussianStep a L F) := by
  apply LipschitzWith.of_dist_le_mul
  intro H K
  let μ := stdGaussian (FiniteStateGaussianInput I)
  let f : FiniteStateGaussianInput I → ℝ := fun z => F (H + L z)
  let g : FiniteStateGaussianInput I → ℝ := fun z => F (K + L z)
  have hfe : Integrable (fun z => Real.exp (a * f z)) μ :=
    integrable_exp_finiteStateGaussian_lipschitz F hF L H a
  have hge : Integrable (fun z => Real.exp (a * g z)) μ :=
    integrable_exp_finiteStateGaussian_lipschitz F hF L K a
  haveI := isProbabilityMeasure_tilted hge
  have hh := sourceLogAverage_sub_tilted_all μ a f g
    (integrable_finiteStateGaussian_lipschitz F hF L H)
    (integrable_finiteStateGaussian_lipschitz F hF L K) hfe hge
  have hb (z : FiniteStateGaussianInput I) : |f z - g z| ≤ (C : ℝ) * ‖H - K‖ := by
    have hd := hF.norm_sub_le (H + L z) (K + L z)
    simpa only [add_sub_add_right_eq_sub, Real.norm_eq_abs, f, g] using hd
  have hm : Measurable (fun z => f z - g z) :=
    ((hF.continuous.comp (by fun_prop)).sub (hF.continuous.comp (by fun_prop))).measurable
  have hbound := sourceLogAverage_abs_le (μ.tilted (fun z => a * g z))
    (fun z => f z - g z) hm ((C : ℝ) * ‖H - K‖)
    (mul_nonneg C.coe_nonneg (norm_nonneg _)) hb a ha
  rw [← hh] at hbound
  simpa only [finiteStateGaussianStep, Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, μ, f, g] using hbound

theorem finiteStateGaussianCascade_lipschitz (F : FiniteStateField S → ℝ)
    {C : NNReal} (hF : LipschitzWith C F) (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (j : ℕ) :
    LipschitzWith C (finiteStateGaussianCascade a L F j) := by
  induction j with
  | zero => exact hF
  | succ j ih => exact finiteStateGaussianStep_lipschitz _ ih (a j) (ha j) (L j)


theorem finiteStateGaussianTerminal_lipschitz [Nonempty S] (V : S → ℝ) :
    LipschitzWith 1 (SpinGlass.AT.gtStateLogPartition V) := by
  apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · exact (SpinGlass.AT.contDiff_gtStateLogPartition V).differentiable (by simp)
  · intro H
    exact_mod_cast SpinGlass.AT.norm_fderiv_gtStateLogPartition_le_one V H

theorem finiteStateGaussianTerminalCascade_lipschitz [Nonempty S]
    (V : S → ℝ) (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (j : ℕ) :
    LipschitzWith 1 (finiteStateGaussianTerminalCascade V a L j) :=
  finiteStateGaussianCascade_lipschitz _ (finiteStateGaussianTerminal_lipschitz V) a ha L j

end FourPapersCommon
