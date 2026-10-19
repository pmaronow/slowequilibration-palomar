module

public import SphericalAging.FlowTerminalSpatialC2

public section
/-! Joint continuity of the actual spatial terminal Hessian, including
nonnegative time zero, from the genuine second variational SDE. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.FlowTerminalHessianContinuity
open HardSphereDynamics LocalSDE FlowTerminalDerivative FlowTerminalSecondDerivative
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
section Flow
variable (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms : ℝ≥0}
  {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
  (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
  (hbd : ∀ i,LipschitzWith Lb (fderiv ℝ (b i)))
  (hsd : ∀ i j,LipschitzWith Ls (fderiv ℝ (s i j)))
  (hbd2 : ∀ i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
  (hsd2 : ∀ i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
  (T : ℝ≥0) (hT : 0<T)
include hbg hsg hbd hsd hbd2 hsd2 hT

theorem response_second_fderiv_apply (x : State N) (t : ℝ≥0) (w v : State N) :
    fderiv ℝ (fun y => stateResponse (NullAugmentation.driver D₀) hbg hsg hb hs y T t) x w v=
      SecondVariationalSDE.terminal (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
        (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T w v t := by
  have hc := (FlowTerminalSpatialC2.stateResponse_contDiff_one
    D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT t).differentiable (by norm_num)
  have hh := congrArg (fun A => A w)
    (stateResponse_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x T t hT v).fderiv
  rw [fderiv_clm_apply hc.differentiableAt (differentiableAt_const v)] at hh
  rw [(hasFDerivAt_const v x).fderiv] at hh
  simpa only [ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply,
    stateResponseSecondOperator_eq_terminal] using hh

theorem response_second_fderiv_joint_continuous : Continuous
    (fun z : ℝ≥0 × State N => fderiv ℝ
      (fun x => stateResponse (NullAugmentation.driver D₀) hbg hsg hb hs x T z.1) z.2) := by
  apply continuous_clm_apply.mpr
  intro w
  apply continuous_clm_apply.mpr
  intro v
  exact (SecondTerminalContinuity.terminal_joint_continuous
    D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT w v).congr
    (fun z => (response_second_fderiv_apply D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT z.2 z.1 w v).symm)

theorem stateClass_second_fderiv_joint_continuous : Continuous
    (fun z : ℝ≥0 × State N => fderiv ℝ
      (fderiv ℝ (fun x => stateClass (NullAugmentation.driver D₀) hb hs x T z.1)) z.2) := by
  have he (t : ℝ≥0) : fderiv ℝ (fun x => stateClass (NullAugmentation.driver D₀) hb hs x T t)=
      fun x => stateResponse (NullAugmentation.driver D₀) hbg hsg hb hs x T t :=
    funext (fun x => (stateClass_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd x T t hT).fderiv)
  exact (response_second_fderiv_joint_continuous D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT).congr
    (fun z => by rw [he])
end Flow
end SphericalAging.FlowTerminalHessianContinuity
