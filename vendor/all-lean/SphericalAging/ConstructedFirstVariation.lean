module

public import SphericalAging.HessianQuadraticSource

public section

/-! The actual continuous first variational process in every initial
direction, with true product-time L⁴ moments. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace ContDiff
namespace SphericalAging.ConstructedFirstVariation
open HardSphereDynamics LocalSDE PredictableLinearCoefficient StochasticFlowDerivative
open LinearSDETimeFourthMoment
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
section Flow
variable (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
  {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
  (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
  (x : State N) (T : ℝ≥0)

@[expose] def process (v : State N) : ℝ≥0 → Ω → State N :=
  LinearVariationalSDE.version D (StochasticFlowDerivative.driftRows D hbg hb hs x T)
    (StochasticFlowDerivative.noiseRows D hsg hb hs x T) v T
    (StochasticFlowDerivative.response D hbg hsg hb hs x T v)

theorem process_strongSolution (v : State N) :
    LinearVariationalSDE.IsStrongSolutionOn (StochasticFlowDerivative.driftRows D hbg hb hs x T)
      (StochasticFlowDerivative.noiseRows D hsg hb hs x T) D v (process D hbg hsg hb hs x T v) T := by
  apply LinearVariationalSDE.strongSolution_of_fixedPoint
  exact LinearVariationalSDE.sourceClass_fixedPoint D _ _ T _

theorem process_adapted (v : State N) : StronglyAdapted F (process D hbg hsg hb hs x T v) :=
  (process_strongSolution D hbg hsg hb hs x T v).1

theorem process_continuous (v : State N) :
    ∀ᵐ omega ∂P,Continuous (fun t => process D hbg hsg hb hs x T v t omega) :=
  (process_strongSolution D hbg hsg hb hs x T v).2.1

theorem process_timeCut (v : State N) :
    ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun q => process D hbg hsg hb hs x T v q.1 q.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        (StochasticFlowDerivative.response D hbg hsg hb hs x T v : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) := by
  apply LinearVariationalSDE.version_timeCut_eq_fixedPoint_ae
  exact LinearVariationalSDE.sourceClass_fixedPoint D _ _ T _

theorem process_time_fourthMoment
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A) (v : State N) :
    MemLp (stateTimeCut (process D hbg hsg hb hs x T v) T) 4 (nonnegativeLebesgueMeasure.prod P) ∧
      (∫ q,‖stateTimeCut (process D hbg hsg hb hs x T v) T q‖^4 ∂nonnegativeLebesgueMeasure.prod P) ≤
        (T : ℝ)*momentConstant N Kb Ks T v :=
  linear_solution_time_fourthMoment (process_strongSolution D hbg hsg hb hs x T v) hnull

end Flow
end SphericalAging.ConstructedFirstVariation
