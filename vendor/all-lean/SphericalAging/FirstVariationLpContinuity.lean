module

public import SphericalAging.FirstVariationDifferenceLpBounds

public section
/-! Genuine fourth-norm continuity of the constructed first responses. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.FirstVariationLpContinuity
open HardSphereDynamics LocalSDE FirstVariationDifferenceLpBounds FlowLinearizationLpBounds
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem differenceCut_lpNorm_four_tendsto_zero (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
    (hbd : ∀ i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀ i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (x : State N) (T : ℝ≥0) (hT : 0<T) (v : State N) :
    Tendsto (fun y => lpNorm (differenceCut (NullAugmentation.driver D₀) hbg hsg hb hs x y T v) 4
      (nonnegativeLebesgueMeasure.prod P)) (𝓝 x) (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := difference_four_bound D₀ hbg hsg hb hs hbd hsd x T hT
  let B := 2*eighthNormConstant N Kb Ks T*‖v‖
  have hc : Continuous (fun y : State N => (C*‖y-x‖*‖v‖)^((1 : ℝ)/3)*B^((2 : ℝ)/3)) := by
    apply Continuous.mul _ continuous_const
    apply Continuous.rpow_const ((continuous_const.mul (continuous_id.sub continuous_const).norm).mul continuous_const)
    intro y;exact .inr (by norm_num)
  have ht : Tendsto (fun y : State N => (C*‖y-x‖*‖v‖)^((1 : ℝ)/3)*B^((2 : ℝ)/3)) (𝓝 x) (𝓝 0) := by
    simpa only [sub_self,norm_zero,mul_zero,Real.zero_rpow (by norm_num : ((1 : ℝ)/3)≠0),zero_mul] using hc.tendsto x
  exact squeeze_zero (fun _ => lpNorm_nonneg) (fun y => (hbound y v).2) ht
end SphericalAging.FirstVariationLpContinuity
