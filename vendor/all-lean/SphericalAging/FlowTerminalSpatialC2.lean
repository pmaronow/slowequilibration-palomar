module

public import SphericalAging.SecondTerminalContinuity

public section
/-! Genuine C² initial-state regularity of actual terminal L² flows. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.FlowTerminalSpatialC2
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

theorem stateResponse_apply_contDiff_one (t : ℝ≥0) (v : State N) :
    ContDiff ℝ 1 (fun x => stateResponse (NullAugmentation.driver D₀) hbg hsg hb hs x T t v) := by
  have hc := (SecondTerminalContinuity.stateResponseSecondOperator_joint_continuous
    D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT v).comp
    ((continuous_const (y := t)).prodMk (continuous_id : Continuous (fun x : State N => x)))
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨fun x => stateResponseSecondOperator (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
    (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T t v,?_,?_⟩
  · exact hc.congr (fun x => rfl)
  · intro x
    exact stateResponse_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x T t hT v

theorem stateResponse_contDiff_one (t : ℝ≥0) :
    ContDiff ℝ 1 (fun x => stateResponse (NullAugmentation.driver D₀) hbg hsg hb hs x T t) :=
  contDiff_clm_apply_iff.mpr (stateResponse_apply_contDiff_one D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT t)

theorem stateClass_contDiff_two (t : ℝ≥0) :
    ContDiff ℝ 2 (fun x => stateClass (NullAugmentation.driver D₀) hb hs x T t) := by
  apply contDiff_succ_iff_hasFDerivAt (n := 1) |>.mpr
  exact ⟨fun x => stateResponse (NullAugmentation.driver D₀) hbg hsg hb hs x T t,
    stateResponse_contDiff_one D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT t,
    fun x => stateClass_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd x T t hT⟩
end Flow
end SphericalAging.FlowTerminalSpatialC2
