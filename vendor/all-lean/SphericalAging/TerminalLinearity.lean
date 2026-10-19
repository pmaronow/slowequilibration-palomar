module

public import SphericalAging.PredictableTerminalOperators
public import SphericalAging.StochasticFlowDerivative

public section

set_option backward.privateInPublic true

/-! Genuine continuous linear full-filtration terminal drift, Itô, basis
inclusion and constant-initial-state operators. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.TerminalLinearity
open HardSphereDynamics PredictableTerminalOperators PredictableItoTime PredictableDriftTime
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

private def additiveOfSub {E G : Type*} [AddCommGroup E] [AddCommGroup G]
    (f : E → G) (hf : ∀ x y,f (x-y)=f x-f y) : E →+ G where
  toFun := f
  map_zero' := by simpa only [sub_self] using hf 0 0
  map_add' x y := by
    have h := hf (x+y) y
    rw [add_sub_cancel_right] at h
    exact (eq_sub_iff_add_eq.mp h).symm

@[expose]  def driftTerminalOperator (T t : ℝ≥0) : PredictableProcessL2 F P →L[ℝ] RandomL2 P :=
  (additiveOfSub (driftTerminal T t) (driftTerminal_sub T t)).toRealLinearMap (by
    change Continuous (driftTerminal (F := F) (P := P) T t)
    exact (driftTerminal_lipschitz T t).continuous)

 @[simp] theorem driftTerminalOperator_apply (T t : ℝ≥0) (U : PredictableProcessL2 F P) :
    driftTerminalOperator T t U=driftTerminal T t U := rfl

@[expose]  def itoTerminalOperator (D : BrownianDriver N P F) (j : Fin N) (t : ℝ≥0) :
    PredictableProcessL2 F P →L[ℝ] RandomL2 P :=
  (FourPapersCommon.FilteredBrownian.naturalItoIntegral (D.brownian j).toIsPreBrownianReal
    (D.coordinateStronglyMeasurable j) (D.filtered j)).comp
    (FourPapersCommon.FilteredBrownian.predictableTimeRestrictCLM F t)

 @[simp] theorem itoTerminalOperator_apply (D : BrownianDriver N P F) (j : Fin N)
    (t : ℝ≥0) (U : PredictableProcessL2 F P) : itoTerminalOperator D j t U=
      FourPapersCommon.FilteredBrownian.naturalItoProcess (D.brownian j).toIsPreBrownianReal
        (D.coordinateStronglyMeasurable j) (D.filtered j) U t := rfl

@[expose]  def stateTerminalInclusion (i : Fin N) : RandomL2 P →L[ℝ] Lp (State N) 2 P :=
  (ContinuousLinearMap.toSpanSingleton ℝ (basisVector i)).compLpL 2 P

@[expose]  def initialTerminalOperator : State N →L[ℝ] Lp (State N) 2 P :=
  (Lp.const 2 P).toRealLinearMap (by
    apply LipschitzWith.continuous (K := 1)
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_eq_norm,NNReal.coe_one,one_mul,← (Lp.const 2 P).map_sub]
    simpa using Lp.norm_const_le 2 P (x-y))

 @[simp] theorem initialTerminalOperator_apply (x : State N) :
    initialTerminalOperator (P := P) x=Lp.const 2 P x := rfl

@[expose]  def coefficientOperator {K : ℝ≥0}
    (a : PredictableLinearCoefficient.Coefficient (N := N) (F := F) (P := P) K) :
    PredictableStateL2 N F P →L[ℝ] PredictableProcessL2 F P :=
  LinearMap.mkContinuous
    {toFun := PredictableLinearCoefficient.apply a
     map_add' := PredictableLinearCoefficient.apply_add a
     map_smul' := PredictableLinearCoefficient.apply_smul a}
    K (PredictableLinearCoefficient.norm_apply_le a)

 @[simp] theorem coefficientOperator_apply {K : ℝ≥0}
    (a : PredictableLinearCoefficient.Coefficient (N := N) (F := F) (P := P) K)
    (U : PredictableStateL2 N F P) : coefficientOperator a U=PredictableLinearCoefficient.apply a U := rfl
end SphericalAging.TerminalLinearity
