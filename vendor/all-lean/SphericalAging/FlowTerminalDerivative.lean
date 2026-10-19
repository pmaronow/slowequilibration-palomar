module

public import SphericalAging.FlowCoefficientDerivative
public import SphericalAging.TerminalStateRepresentation

public section

/-! Actual fixed-terminal-time L² initial-state Fréchet derivative of the
constructed SDE, with a genuine strong variational-SDE representative. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.FlowTerminalDerivative
set_option maxHeartbeats 2000000
open HardSphereDynamics LocalSDE VariationalCoefficients PredictableLinearCoefficient
open StochasticFlowDerivative TerminalLinearity TerminalStateRepresentation FlowCoefficientDerivative
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose]  def stateClass (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
    (x : State N) (T t : ℝ≥0) : Lp (State N) 2 P :=
  terminalClass D x (fun i => predictableCoefficient (hb i) (GlobalSDE.horizonClass D hb hs x T) T)
    (fun i j => predictableCoefficient (hs i j) (GlobalSDE.horizonClass D hb hs x T) T) T t

@[expose]  def stateResponse (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
    (x : State N) (T t : ℝ≥0) : State N →L[ℝ] Lp (State N) 2 P :=
  initialTerminalOperator+∑ i,(stateTerminalInclusion i).comp
    (((driftTerminalOperator T t).comp (coefficientOperator (driftRows D hbg hb hs x T i))).comp
      (response D hbg hsg hb hs x T)+
    ∑ j,((itoTerminalOperator D j t).comp (coefficientOperator (noiseRows D hsg hb hs x T i j))).comp
      (response D hbg hsg hb hs x T))

 theorem stateClass_ae (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
    (x : State N) (T t : ℝ≥0) : stateClass D hb hs x T t =ᵐ[P]
      GlobalSDE.horizonProcess D hb hs x T t :=
  nonlinear_terminalClass_ae D hb hs x T t _

/-- True fixed-terminal-time Fréchet differentiation of the actual
constructed nonlinear process, in L²(P). -/
 theorem stateClass_hasFDerivAt_initial (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
    (hbd : ∀ i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀ i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (x : State N) (T t : ℝ≥0) (hT : 0 < T) :
    HasFDerivAt (fun y : State N => stateClass (NullAugmentation.driver D₀) hb hs y T t)
      (stateResponse (NullAugmentation.driver D₀) hbg hsg hb hs x T t) x := by
  classical
  let D := NullAugmentation.driver D₀
  have hbi (i : Fin N) : HasFDerivAt
      (fun y : State N => predictableCoefficient (hb i) (GlobalSDE.horizonClass D hb hs y T) T)
      ((coefficientOperator (driftRows D hbg hb hs x T i)).comp (response D hbg hsg hb hs x T)) x :=
    coefficient_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd (hbg i) (hb i) (hbd i) x T hT
  have hsi (i j : Fin N) : HasFDerivAt
      (fun y : State N => predictableCoefficient (hs i j) (GlobalSDE.horizonClass D hb hs y T) T)
      ((coefficientOperator (noiseRows D hsg hb hs x T i j)).comp (response D hbg hsg hb hs x T)) x :=
    coefficient_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd (hsg i j) (hs i j) (hsd i j) x T hT
  have hdi (i : Fin N) := (driftTerminalOperator T t).hasFDerivAt.comp x (hbi i)
  have hni (i j : Fin N) := (itoTerminalOperator D j t).hasFDerivAt.comp x (hsi i j)
  have hrow (i : Fin N) := (stateTerminalInclusion (P := P) i).hasFDerivAt.comp x
    ((hdi i).add (HasFDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) => hni i j)))
  have hresult := (initialTerminalOperator (N := N) (P := P)).hasFDerivAt.add
    (HasFDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => hrow i))
  convert hresult using 1
  · funext y
    rfl
  · simp only [stateResponse,ContinuousLinearMap.comp_assoc]
    rfl

 theorem stateResponse_ae (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
    (x v : State N) (T t : ℝ≥0) : stateResponse D hbg hsg hb hs x T t v =ᵐ[P]
      LinearVariationalSDE.version D (driftRows D hbg hb hs x T) (noiseRows D hsg hb hs x T)
        v T (response D hbg hsg hb hs x T v) t := by
  have he : stateResponse D hbg hsg hb hs x T t v = terminalClass D v
      (fun i => apply (driftRows D hbg hb hs x T i) (response D hbg hsg hb hs x T v))
      (fun i j => apply (noiseRows D hsg hb hs x T i j) (response D hbg hsg hb hs x T v)) T t := by
    simp only [stateResponse,terminalClass,add_apply,sum_apply,
      ContinuousLinearMap.comp_apply,coefficientOperator_apply]
  rw [he]
  exact linear_terminalClass_ae D _ _ v T t _

/-- One genuine continuous adapted strong Jacobian SDE representative
realizes every terminal derivative of the constructed nonlinear SDE. -/
 theorem exists_terminalResponse_solution (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
    (x v : State N) (T : ℝ≥0) : ∃ Y,
      LinearVariationalSDE.IsStrongSolutionOn (driftRows D hbg hb hs x T) (noiseRows D hsg hb hs x T) D v Y T ∧
      ∀ t,stateResponse D hbg hsg hb hs x T t v =ᵐ[P] Y t := by
  let a := driftRows D hbg hb hs x T
  let z := noiseRows D hsg hb hs x T
  let U := response D hbg hsg hb hs x T v
  have hU := LinearVariationalSDE.sourceClass_fixedPoint D a z T (initialClass v T)
  exact ⟨LinearVariationalSDE.version D a z v T U,
    LinearVariationalSDE.strongSolution_of_fixedPoint D a z v T U hU,
    fun t => stateResponse_ae D hbg hsg hb hs x v T t⟩
end SphericalAging.FlowTerminalDerivative
