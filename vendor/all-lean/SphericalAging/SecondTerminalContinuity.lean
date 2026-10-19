module

public import SphericalAging.SecondVariationContinuity
public import SphericalAging.FlowCoefficientJointApplicationContinuity
public import SphericalAging.FlowTerminalSecondDerivative
public import SphericalAging.TerminalTimeContinuity

public section
/-! True second terminal responses are jointly continuous in terminal time
and initial state, including time zero. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.SecondTerminalContinuity
open HardSphereDynamics LocalSDE StochasticFlowDerivative TerminalLinearity
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
include hbd2 hsd2 hT

theorem terminal_joint_continuous (v w : State N) : Continuous
    (fun z : ℝ≥0 × State N => SecondVariationalSDE.terminal (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) z.2 T v w z.1) := by
  classical
  let D := NullAugmentation.driver D₀
  have hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[NullAugmentation.augment F P 0] A :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  let Q := fun x => SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull x T v w
  let R := fun x i => PredictableLinearCoefficient.apply (driftRows D hbg hb hs x T i) (Q x)+
    HessianInitialSource.source D hbg hsg hb hs hnull x T (b i) (hbg i) (hbd i) v w
  let S := fun x i j => PredictableLinearCoefficient.apply (noiseRows D hsg hb hs x T i j) (Q x)+
    HessianInitialSource.source D hbg hsg hb hs hnull x T (s i j) (hsg i j) (hsd i j) v w
  have hQ : Continuous Q := SecondVariationContinuity.responseClass_continuous D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT v w
  have hR (i : Fin N) : Continuous (fun x => R x i) :=
    (FlowCoefficientJointApplicationContinuity.apply_row_of_continuous D hb hs T (b i) (hbg i) (hb i) (hbd i) Q hQ).add
      (HessianSourceContinuity.source_continuous D₀ hbg hsg hb hs hbd hsd T hT (b i) (hbg i) (hbd i) (hbd2 i) v w)
  have hS (i j : Fin N) : Continuous (fun x => S x i j) :=
    (FlowCoefficientJointApplicationContinuity.apply_row_of_continuous D hb hs T (s i j) (hsg i j) (hs i j) (hsd i j) Q hQ).add
      (HessianSourceContinuity.source_continuous D₀ hbg hsg hb hs hbd hsd T hT (s i j) (hsg i j) (hsd i j) (hsd2 i j) v w)
  have hd (i : Fin N) : Continuous (fun z : ℝ≥0 × State N => driftTerminalOperator T z.1 (R z.2 i)) := by
    have hh := (TerminalTimeContinuity.driftTerminal_joint_continuous (F := NullAugmentation.augment F P) (P := P) T).comp
      (continuous_fst.prodMk ((hR i).comp continuous_snd))
    exact hh.congr (fun z => rfl)
  have hn (i j : Fin N) : Continuous (fun z : ℝ≥0 × State N => itoTerminalOperator D j z.1 (S z.2 i j)) := by
    have hh := (TerminalTimeContinuity.itoTerminal_joint_continuous D j).comp
      (continuous_fst.prodMk ((hS i j).comp continuous_snd))
    exact hh.congr (fun z => rfl)
  have hh : Continuous (fun z : ℝ≥0 × State N => ∑ i : Fin N,stateTerminalInclusion i
      (driftTerminalOperator T z.1 (R z.2 i)+∑ j : Fin N,itoTerminalOperator D j z.1 (S z.2 i j))) := by
    apply continuous_finset_sum
    intro i _
    apply (stateTerminalInclusion i).continuous.comp
    exact (hd i).add (continuous_finset_sum _ (fun j _ => hn i j))
  exact hh.congr (fun z => by
    simp only [SecondVariationalSDE.terminal,L2AffineVariationalSolution.terminal,
      TerminalStateRepresentation.terminalClass,initialTerminalOperator_apply,map_zero,zero_add]
    rfl)

theorem stateResponseSecondOperator_joint_continuous (v : State N) : Continuous
    (fun z : ℝ≥0 × State N => FlowTerminalSecondDerivative.stateResponseSecondOperator (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) z.2 T z.1 v) := by
  apply continuous_clm_apply.mpr
  intro w
  exact (terminal_joint_continuous D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT w v).congr
    (fun z => (FlowTerminalSecondDerivative.stateResponseSecondOperator_eq_terminal
      (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) z.2 T z.1 v w).symm)
end Flow
end SphericalAging.SecondTerminalContinuity
