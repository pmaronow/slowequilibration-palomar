module
public import FourPapersCommon.SignedControlEndpoints
public import FourPapersCommon.SignedFeedbackState

@[expose] public section

/-! Actual signed scalar Gaussian control representation. The extremizing control
is constructed from the genuine logarithmic Gaussian heat flow. The verification
identity is an exact square gap, rather than an assumed variational formula. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus FRSB
open scoped Topology NNReal
namespace FourPapersCommon
open Paper
set_option maxHeartbeats 1000000

def scalarBrownianPayoff (F : ℝ → ℝ) (m x : ℝ)
    (A : ℝ → BrownianSample → ℝ) : ℝ :=
  (∫ sample,F (scalarControlledState m x A 1 sample) ∂canonicalBrownianMeasure)-
    m/2*(∫ sample,(∫ s in 0..(1 : ℝ),A s sample^2) ∂canonicalBrownianMeasure)

def scalarBrownianSquareGap (F : ℝ → ℝ) (m x : ℝ)
    (A : ℝ → BrownianSample → ℝ) : ℝ :=
  ∫ sample,(∫ s in 0..(1 : ℝ),
    (A s sample-signedHeatLogDx (fun y=>Real.exp (m*F y)) m (1-s)
      (scalarControlledState m x A s.toNNReal sample))^2) ∂canonicalBrownianMeasure

theorem scalarBrownianSquareGap_nonneg (F : ℝ → ℝ) (m x : ℝ)
    (A : ℝ → BrownianSample → ℝ) : 0 ≤ scalarBrownianSquareGap F m x A := by
  unfold scalarBrownianSquareGap
  apply MeasureTheory.integral_nonneg
  intro sample
  exact intervalIntegral.integral_nonneg_of_forall
    (by norm_num : (0:ℝ) ≤ 1) (fun s=>sq_nonneg _)

theorem integrable_scalarControlEnergy (A : ℝ → BrownianSample → ℝ)
    (hA : IsScalarBrownianControl A) :
    Integrable (fun sample=>∫ s in 0..(1 : ℝ),A s sample^2) canonicalBrownianMeasure := by
  obtain ⟨K,hK⟩ := hA.bounded
  apply integrable_bounded_intervalIntegral canonicalBrownianMeasure _
    (hA.measurable.pow_const 2) ((K:ℝ)^2) _ 0 1 (by norm_num)
  intro s sample
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hK s sample) 2

theorem scalarBrownianPayoff_squareGap {F : ℝ → ℝ} (hF : SignedScalarDatum F)
    (m x : ℝ) (hm : m ≠ 0) (A : ℝ → BrownianSample → ℝ) (hA : IsScalarBrownianControl A) :
    scalarBrownianPayoff F m x A=
      signedHeatLog (fun y=>Real.exp (m*F y)) m 1 x-m/2*scalarBrownianSquareGap F m x A := by
  obtain ⟨L,hL⟩ := hF.lipschitz
  obtain ⟨K,hK⟩ := hA.bounded
  let R := fun s sample=>(A s sample-signedHeatLogDx (fun y=>Real.exp (m*F y)) m (1-s)
    (scalarControlledState m x A s.toNNReal sample))^2
  have hmR : Measurable (Function.uncurry R) := by
    have hDx := (continuous_signedHeatLog_jets (hF.expHeatDatum m) m
      (fun v y=>(gaussianHeatFlow_exp_pos hF m v y).ne')).2.1
    have hX := (measurable_scalarControlledState m x A hA).comp
      (measurable_real_toNNReal.prodMap measurable_id)
    exact (hA.measurable.sub (hDx.measurable.comp
      ((measurable_const.sub measurable_fst).prodMk hX))).pow_const 2
  have hR (s : ℝ) (sample : BrownianSample) : ‖R s sample‖ ≤ ((K:ℝ)+L)^2 := by
    have hh : ‖A s sample-signedHeatLogDx (fun y=>Real.exp (m*F y)) m (1-s)
      (scalarControlledState m x A s.toNNReal sample)‖ ≤ (K:ℝ)+L :=
      (norm_sub_le _ _).trans (add_le_add (hK s sample)
        (norm_signedHeatLogDx_exp_le hF L hL m _ _ hm))
    change ‖(A s sample-signedHeatLogDx (fun y=>Real.exp (m*F y)) m (1-s)
      (scalarControlledState m x A s.toNNReal sample))^2‖ ≤ ((K:ℝ)+L)^2
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hh 2
  have hiR := integrable_bounded_intervalIntegral canonicalBrownianMeasure R hmR
    (((K:ℝ)+L)^2) hR 0 1 (by norm_num)
  have hiA := integrable_scalarControlEnergy A hA
  have hiF := integrable_lipschitz_scalarControlledState m x A hA 1 F L hL
  have hcostBound := norm_signedControlGapSource_le hF m x hm A K L hK hL
  have hiCost := integrable_bounded_intervalIntegral canonicalBrownianMeasure _
    (measurable_signedControlGapSource hF m x A hA) _ hcostBound 0 1 (by norm_num)
  have he (sample : BrownianSample) :
      (∫ s in 0..(1 : ℝ),signedControlGapSource F m x A s sample)=
        m/2*((∫ s in 0..(1 : ℝ),A s sample^2)-(∫ s in 0..(1 : ℝ),R s sample)) := by
    have ha : IntervalIntegrable (fun s=>A s sample^2) volume 0 1 :=
      ((hA.continuous_paths sample).pow 2).intervalIntegrable 0 1
    have hr : IntervalIntegrable (fun s=>R s sample) volume 0 1 := by
      apply (intervalIntegrable_const (c:=((K:ℝ)+L)^2)).mono_fun'
        (hmR.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      exact .of_forall (fun s=>hR s sample)
    simp only [signedControlGapSource,R]
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_sub ha hr]
  have hclosed := signedControl_squareGap_closed hF m x hm A hA
  rw [integral_sub hiF hiCost] at hclosed
  simp_rw [he] at hclosed
  rw [integral_const_mul,integral_sub hiA hiR] at hclosed
  unfold scalarBrownianPayoff scalarBrownianSquareGap
  change (∫ sample,F (scalarControlledState m x A 1 sample) ∂canonicalBrownianMeasure)-
    m/2*(∫ sample,(∫ s in 0..(1 : ℝ),A s sample^2) ∂canonicalBrownianMeasure)=
      signedHeatLog (fun y=>Real.exp (m*F y)) m 1 x-
        m/2*(∫ sample,(∫ s in 0..(1 : ℝ),R s sample) ∂canonicalBrownianMeasure)
  linarith

theorem scalarBrownianPayoff_le_heat_of_pos {F : ℝ → ℝ} (hF : SignedScalarDatum F)
    (m x : ℝ) (hm : 0 < m) (A : ℝ → BrownianSample → ℝ) (hA : IsScalarBrownianControl A) :
    scalarBrownianPayoff F m x A ≤ signedHeatLog (fun y=>Real.exp (m*F y)) m 1 x := by
  rw [scalarBrownianPayoff_squareGap hF m x hm.ne' A hA]
  exact sub_le_self _ (mul_nonneg (by positivity) (scalarBrownianSquareGap_nonneg F m x A))

theorem heat_le_scalarBrownianPayoff_of_neg {F : ℝ → ℝ} (hF : SignedScalarDatum F)
    (m x : ℝ) (hm : m < 0) (A : ℝ → BrownianSample → ℝ) (hA : IsScalarBrownianControl A) :
    signedHeatLog (fun y=>Real.exp (m*F y)) m 1 x ≤ scalarBrownianPayoff F m x A := by
  rw [scalarBrownianPayoff_squareGap hF m x hm.ne A hA]
  have hh : m/2*scalarBrownianSquareGap F m x A ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (scalarBrownianSquareGap_nonneg F m x A)
  linarith

theorem exists_scalarBrownianPayoff_eq_heat {F : ℝ → ℝ} (hF : SignedScalarDatum F)
    (m x : ℝ) (hm : m ≠ 0) :
    ∃ A : ℝ → BrownianSample → ℝ,IsScalarBrownianControl A ∧
      scalarBrownianPayoff F m x A=signedHeatLog (fun y=>Real.exp (m*F y)) m 1 x := by
  obtain ⟨A,hA,hfeedback⟩ := exists_actual_signedHeatFeedback hF m x hm
  refine ⟨A,hA,?_⟩
  rw [scalarBrownianPayoff_squareGap hF m x hm A hA]
  have he : scalarBrownianSquareGap F m x A=0 := by
    unfold scalarBrownianSquareGap
    have hi (sample : BrownianSample) :
        (∫ s in 0..(1 : ℝ),(A s sample-signedHeatLogDx (fun y=>Real.exp (m*F y)) m (1-s)
          (scalarControlledState m x A s.toNNReal sample))^2)=0 := by
      calc
        _ = ∫ s in 0..(1 : ℝ),(0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro s hs
          have hsI : s∈Icc (0:ℝ) 1 := by
            simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hs
          dsimp only
          rw [hfeedback s hsI sample,sub_self,zero_pow (by norm_num : 2 ≠ 0)]
        _ = 0 := by simp
    simp_rw [hi]
    simp
  rw [he,mul_zero,sub_zero]

end FourPapersCommon
