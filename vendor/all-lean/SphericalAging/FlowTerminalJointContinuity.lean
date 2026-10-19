module

public import SphericalAging.TerminalFamilyContinuity
public import SphericalAging.FirstCoefficientSecondDerivative

public section
/-! Actual terminal flow values and first derivatives are jointly
continuous in nonnegative terminal time and initial state. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.FlowTerminalJointContinuity
open HardSphereDynamics LocalSDE FlowTerminalDerivative TerminalLinearity
open StochasticFlowDerivative PredictableLinearCoefficient PredictableItoTime
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
include hbg hsg hbd hsd hT

theorem stateClass_joint_continuous : Continuous
    (fun z : ℝ≥0 × State N => stateClass (NullAugmentation.driver D₀) hb hs z.2 T z.1) := by
  let D := NullAugmentation.driver D₀
  have hR (i : Fin N) : Continuous (fun x => predictableCoefficient (hb i) (GlobalSDE.horizonClass D hb hs x T) T) :=
    continuous_iff_continuousAt.mpr (fun x =>
      (FlowCoefficientDerivative.coefficient_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd (hbg i) (hb i) (hbd i) x T hT).continuousAt)
  have hS (i j : Fin N) : Continuous (fun x => predictableCoefficient (hs i j) (GlobalSDE.horizonClass D hb hs x T) T) :=
    continuous_iff_continuousAt.mpr (fun x =>
      (FlowCoefficientDerivative.coefficient_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd (hsg i j) (hs i j) (hsd i j) x T hT).continuousAt)
  exact TerminalFamilyContinuity.terminalClass_joint_continuous D T id
    (fun x i => predictableCoefficient (hb i) (GlobalSDE.horizonClass D hb hs x T) T)
    (fun x i j => predictableCoefficient (hs i j) (GlobalSDE.horizonClass D hb hs x T) T)
    continuous_id hR hS

include hbd2 hsd2 in
 theorem stateResponse_apply_joint_continuous (v : State N) : Continuous
    (fun z : ℝ≥0 × State N => stateResponse (NullAugmentation.driver D₀) hbg hsg hb hs z.2 T z.1 v) := by
  let D := NullAugmentation.driver D₀
  let R := fun x i => apply (driftRows D hbg hb hs x T i) (response D hbg hsg hb hs x T v)
  let S := fun x i j => apply (noiseRows D hsg hb hs x T i j) (response D hbg hsg hb hs x T v)
  have hR (i : Fin N) : Continuous (fun x => R x i) :=
    continuous_iff_continuousAt.mpr (fun x =>
      (FirstCoefficientSecondDerivative.firstCoefficient_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x T hT
        (b i) (hbg i) (hb i) (hbd i) (hbd2 i) v).continuousAt)
  have hS (i j : Fin N) : Continuous (fun x => S x i j) :=
    continuous_iff_continuousAt.mpr (fun x =>
      (FirstCoefficientSecondDerivative.firstCoefficient_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x T hT
        (s i j) (hsg i j) (hs i j) (hsd i j) (hsd2 i j) v).continuousAt)
  have hh := TerminalFamilyContinuity.terminalClass_joint_continuous D T (fun _ => v) R S continuous_const hR hS
  exact hh.congr (fun z => by
    simp only [TerminalStateRepresentation.terminalClass,stateResponse,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,coefficientOperator_apply]
    rfl)

include hbd2 hsd2 in
 theorem stateResponse_joint_continuous : Continuous
    (fun z : ℝ≥0 × State N => stateResponse (NullAugmentation.driver D₀) hbg hsg hb hs z.2 T z.1) :=
  continuous_clm_apply.mpr (stateResponse_apply_joint_continuous D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT)
end Flow
end SphericalAging.FlowTerminalJointContinuity
