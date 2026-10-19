module

public import SphericalAging.ConstructedFirstVariation
public import SphericalAging.L2AffineVariationalSolution

public section

/-! Actual continuous second variational equations. The quadratic sources
are formed from the genuine first strong responses and the actual Hessians
along the constructed nonlinear flow. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace ContDiff
namespace SphericalAging.SecondVariationalSDE
open HardSphereDynamics LocalSDE PredictableLinearCoefficient
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
section Flow
variable (D : BrownianDriver N P F) {Kb Ks Lb Ls : ℝ≥0}
  {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
  (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
  (hbd : ∀ i,LipschitzWith Lb (fderiv ℝ (b i)))
  (hsd : ∀ i j,LipschitzWith Ls (fderiv ℝ (s i j)))
  (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
  (x : State N) (T : ℝ≥0)

@[expose] def driftSource (v w : State N) (i : Fin N) : PredictableProcessL2 F P :=
  HessianQuadraticSource.source (b i) (hbg i) (hbd i)
    (GlobalSDE.horizonProcess D hb hs x T)
    (ConstructedFirstVariation.process D hbg hsg hb hs x T v)
    (ConstructedFirstVariation.process D hbg hsg hb hs x T w)
    (GlobalSDE.horizonProcess_stronglyAdapted D hb hs x T)
    (ConstructedFirstVariation.process_adapted D hbg hsg hb hs x T v)
    (ConstructedFirstVariation.process_adapted D hbg hsg hb hs x T w)
    (GlobalSDE.horizonProcess_continuous D hb hs x T)
    (ConstructedFirstVariation.process_continuous D hbg hsg hb hs x T v)
    (ConstructedFirstVariation.process_continuous D hbg hsg hb hs x T w) T
    (ConstructedFirstVariation.process_time_fourthMoment D hbg hsg hb hs x T hnull v).1
    (ConstructedFirstVariation.process_time_fourthMoment D hbg hsg hb hs x T hnull w).1

@[expose] def noiseSource (v w : State N) (i j : Fin N) : PredictableProcessL2 F P :=
  HessianQuadraticSource.source (s i j) (hsg i j) (hsd i j)
    (GlobalSDE.horizonProcess D hb hs x T)
    (ConstructedFirstVariation.process D hbg hsg hb hs x T v)
    (ConstructedFirstVariation.process D hbg hsg hb hs x T w)
    (GlobalSDE.horizonProcess_stronglyAdapted D hb hs x T)
    (ConstructedFirstVariation.process_adapted D hbg hsg hb hs x T v)
    (ConstructedFirstVariation.process_adapted D hbg hsg hb hs x T w)
    (GlobalSDE.horizonProcess_continuous D hb hs x T)
    (ConstructedFirstVariation.process_continuous D hbg hsg hb hs x T v)
    (ConstructedFirstVariation.process_continuous D hbg hsg hb hs x T w) T
    (ConstructedFirstVariation.process_time_fourthMoment D hbg hsg hb hs x T hnull v).1
    (ConstructedFirstVariation.process_time_fourthMoment D hbg hsg hb hs x T hnull w).1

@[expose] def responseClass (v w : State N) : PredictableStateL2 N F P :=
  L2AffineVariationalSolution.responseClass D (StochasticFlowDerivative.driftRows D hbg hb hs x T)
    (StochasticFlowDerivative.noiseRows D hsg hb hs x T)
    (driftSource D hbg hsg hb hs hbd hnull x T v w)
    (noiseSource D hbg hsg hb hs hsd hnull x T v w) T

@[expose] def process (v w : State N) : ℝ≥0 → Ω → State N :=
  L2AffineVariationalSolution.process D (StochasticFlowDerivative.driftRows D hbg hb hs x T)
    (StochasticFlowDerivative.noiseRows D hsg hb hs x T)
    (driftSource D hbg hsg hb hs hbd hnull x T v w)
    (noiseSource D hbg hsg hb hs hsd hnull x T v w) T

@[expose] def terminal (v w : State N) (t : ℝ≥0) : Lp (State N) 2 P :=
  L2AffineVariationalSolution.terminal D (StochasticFlowDerivative.driftRows D hbg hb hs x T)
    (StochasticFlowDerivative.noiseRows D hsg hb hs x T)
    (driftSource D hbg hsg hb hs hbd hnull x T v w)
    (noiseSource D hbg hsg hb hs hsd hnull x T v w) T t

theorem process_strongSolution (v w : State N) :
    L2AffineVariationalSolution.IsStrongSolutionOn D
      (StochasticFlowDerivative.driftRows D hbg hb hs x T)
      (StochasticFlowDerivative.noiseRows D hsg hb hs x T) T
      (fun i => HessianQuadraticSource.hessianField (b i)
        (GlobalSDE.horizonProcess D hb hs x T)
        (ConstructedFirstVariation.process D hbg hsg hb hs x T v)
        (ConstructedFirstVariation.process D hbg hsg hb hs x T w))
      (fun i j => HessianQuadraticSource.hessianField (s i j)
        (GlobalSDE.horizonProcess D hb hs x T)
        (ConstructedFirstVariation.process D hbg hsg hb hs x T v)
        (ConstructedFirstVariation.process D hbg hsg hb hs x T w))
      (process D hbg hsg hb hs hbd hsd hnull x T v w) := by
  apply L2AffineVariationalSolution.process_strongSolution
  · intro i
    exact HessianQuadraticSource.source_coe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · intro i j
    exact HessianQuadraticSource.source_coe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem process_timeCut (v w : State N) :
    LinearSDETimeFourthMoment.stateTimeCut (process D hbg hsg hb hs hbd hsd hnull x T v w) T
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        (responseClass D hbg hsg hb hs hbd hsd hnull x T v w :
          Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) :=
  L2AffineVariationalSolution.process_timeCut D _ _ _ _ T

theorem terminal_ae (v w : State N) (t : ℝ≥0) :
    terminal D hbg hsg hb hs hbd hsd hnull x T v w t =ᵐ[P]
      process D hbg hsg hb hs hbd hsd hnull x T v w t :=
  L2AffineVariationalSolution.terminal_ae D _ _ _ _ T t

end Flow
end SphericalAging.SecondVariationalSDE
