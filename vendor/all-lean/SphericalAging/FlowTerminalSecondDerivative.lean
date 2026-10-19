module

public import SphericalAging.FirstCoefficientSecondDerivative

public section
/-! Actual fixed-terminal first responses have genuine second spatial
Fréchet derivatives, realized by the constructed second strong SDE. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.FlowTerminalSecondDerivative
open HardSphereDynamics LocalSDE StochasticFlowDerivative TerminalLinearity FlowTerminalDerivative
open FirstCoefficientSecondDerivative
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
section Definition
variable (D : BrownianDriver N P F) {Kb Ks Lb Ls : ℝ≥0}
  {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
  (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
  (hbd : ∀ i,LipschitzWith Lb (fderiv ℝ (b i)))
  (hsd : ∀ i j,LipschitzWith Ls (fderiv ℝ (s i j)))
  (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
  (x : State N) (T t : ℝ≥0) (v : State N)

@[expose] def stateResponseSecondOperator : State N →L[ℝ] Lp (State N) 2 P :=
  ∑ i,(stateTerminalInclusion i).comp
    ((driftTerminalOperator T t).comp
      (rowSecondOperator D hbg hsg hb hs hbd hsd hnull x T (b i) (hbg i) (hb i) (hbd i) v)+
    ∑ j,(itoTerminalOperator D j t).comp
      (rowSecondOperator D hbg hsg hb hs hbd hsd hnull x T (s i j) (hsg i j) (hs i j) (hsd i j) v))

theorem stateResponseSecondOperator_eq_terminal (w : State N) :
    stateResponseSecondOperator D hbg hsg hb hs hbd hsd hnull x T t v w=
      SecondVariationalSDE.terminal D hbg hsg hb hs hbd hsd hnull x T w v t := by
  simp only [stateResponseSecondOperator,rowSecondOperator,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.add_apply,coefficientOperator_apply,
    SecondVariationBilinear.leftOperator_apply,HessianInitialSource.leftOperator_apply,
    SecondVariationalSDE.terminal,L2AffineVariationalSolution.terminal,
    TerminalStateRepresentation.terminalClass,TerminalLinearity.initialTerminalOperator,
    map_zero,zero_add,L2AffineVariationalSolution.driftRows,L2AffineVariationalSolution.noiseRows]
  rfl
end Definition

theorem stateResponse_hasFDerivAt_initial (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
    (hbd : ∀ i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀ i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (hbd2 : ∀ i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
    (hsd2 : ∀ i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
    (x : State N) (T t : ℝ≥0) (hT : 0<T) (v : State N) :
    HasFDerivAt (fun y => stateResponse (NullAugmentation.driver D₀) hbg hsg hb hs y T t v)
      (stateResponseSecondOperator (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
        (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T t v) x := by
  classical
  let D := NullAugmentation.driver D₀
  have hbi (i : Fin N) := firstCoefficient_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd hbd2 hsd2
    x T hT (b i) (hbg i) (hb i) (hbd i) (hbd2 i) v
  have hsi (i j : Fin N) := firstCoefficient_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd hbd2 hsd2
    x T hT (s i j) (hsg i j) (hs i j) (hsd i j) (hsd2 i j) v
  have hdi (i : Fin N) := (driftTerminalOperator T t).hasFDerivAt.comp x (hbi i)
  have hni (i j : Fin N) := (itoTerminalOperator D j t).hasFDerivAt.comp x (hsi i j)
  have hrow (i : Fin N) := (stateTerminalInclusion (P := P) i).hasFDerivAt.comp x
    ((hdi i).add (HasFDerivAt.fun_sum (fun j (_ : j∈Finset.univ) => hni i j)))
  have hh := (hasFDerivAt_const (initialTerminalOperator (N := N) (P := P) v) x).add
    (HasFDerivAt.fun_sum (fun i (_ : i∈Finset.univ) => hrow i))
  convert hh using 1
  · funext y
    simp only [stateResponse,ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.comp_apply,coefficientOperator_apply]
    rfl
  · simp only [zero_add,stateResponseSecondOperator,ContinuousLinearMap.comp_assoc]
    rfl
end SphericalAging.FlowTerminalSecondDerivative
