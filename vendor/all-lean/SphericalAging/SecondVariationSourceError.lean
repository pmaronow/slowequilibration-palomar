module

public import SphericalAging.SecondVariationPointwiseError
public import SphericalAging.LpProductBounds
public import SphericalAging.HessianInitialSource
public import SphericalAging.FirstVariationDifferenceLpBounds

public section
/-! The literal Jacobian forcing remainder along constructed flow paths.
Its three terms are controlled by actual Lp norms. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.SecondVariationSourceError
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment NonlinearIncrementFourthMoment
open StochasticFlowDerivative PredictableLinearCoefficient
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
section Flow
variable (D : BrownianDriver N P F) {Kb Ks K L M : ℝ≥0}
  {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
  (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
  (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
  (x y : State N) (T : ℝ≥0) (g : State N → ℝ) (hg : ContDiff ℝ ∞ g)
  (hK : LipschitzWith K g) (hL : LipschitzWith L (fderiv ℝ g))

@[expose] def row (z : State N) := VariationalCoefficients.derivativeRow (GlobalSDE.horizonProcess D hb hs z T)
  (GlobalSDE.horizonProcess_stronglyAdapted D hb hs z T)
  (GlobalSDE.horizonProcess_continuous D hb hs z T) hg hK T

@[expose] def sourceError (v : State N) : PredictableProcessL2 F P :=
  apply (row D hb hs T g hg hK y) (response D hbg hsg hb hs y T v)-
  apply (row D hb hs T g hg hK x) (response D hbg hsg hb hs y T v)-
  HessianInitialSource.source D hbg hsg hb hs hnull x T g hg hL (y-x) v

theorem sourceError_bound (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g))) (v : State N) :
    ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      ‖(sourceError D hbg hsg hb hs hnull x y T g hg hK hL v : TimeProcessL2 P) q‖≤
      (M : ℝ)*‖stateTimeCut (increment D hb hs x y T) T q‖^2*
        ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T v) T q‖+
      (L : ℝ)*‖FlowLinearizationLpBounds.remainderCut D hbg hsg hb hs x y T q‖*
        ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T v) T q‖+
      (L : ℝ)*‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T (y-x)) T q‖*
        ‖FirstVariationDifferenceLpBounds.differenceCut D hbg hsg hb hs x y T v q‖ := by
  let U := response D hbg hsg hb hs y T v
  let A := apply (row D hb hs T g hg hK y) U
  let B := apply (row D hb hs T g hg hK x) U
  let C := HessianInitialSource.source D hbg hsg hb hs hnull x T g hg hL (y-x) v
  have hY := ConstructedFirstVariation.process_timeCut D hbg hsg hb hs y T v
  filter_upwards [Lp.coeFn_sub ((A-B : PredictableProcessL2 F P) : TimeProcessL2 P) C,
    Lp.coeFn_sub (A : TimeProcessL2 P) B,
    LinearVariationalSDE.apply_eq_actual hY (row D hb hs T g hg hK y),
    LinearVariationalSDE.apply_eq_actual hY (row D hb hs T g hg hK x),
    HessianInitialSource.source_coe D hbg hsg hb hs hnull x T g hg hL (y-x) v]
    with q hsub hsub' hy hx hc
  change ‖((A-B-C : PredictableProcessL2 F P) : TimeProcessL2 P) q‖≤_
  simp only [Submodule.coe_sub] at hsub ⊢
  rw [hsub,Pi.sub_apply,hsub',Pi.sub_apply,hy,hx,hc]
  by_cases ht : q.1∈Ioc (0 : ℝ≥0) T
  · simp only [row,VariationalCoefficients.derivativeRow,FourPapersCommon.continuousAdaptedTimeCut,
      stateTimeCut,increment,FlowLinearizationLpBounds.remainderCut,
      FirstVariationDifferenceLpBounds.differenceCut,HessianQuadraticSource.hessianField,ht,ite_true]
    rw [←ContinuousLinearMap.sub_apply]
    exact SecondVariationPointwiseError.jacobian_variation_error_bound hg hL hM _ _ _ _ _
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,stateTimeCut,
      FlowLinearizationLpBounds.remainderCut,FirstVariationDifferenceLpBounds.differenceCut,
      ht,ite_false,sub_self,norm_zero,zero_pow (by norm_num : (2 : ℕ)≠0),mul_zero,add_zero,le_refl]

theorem sourceError_norm_le (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g))) (v : State N)
    (hi8 : MemLp (stateTimeCut (increment D hb hs x y T) T) 8 (nonnegativeLebesgueMeasure.prod P))
    (he4 : MemLp (FlowLinearizationLpBounds.remainderCut D hbg hsg hb hs x y T) 4 (nonnegativeLebesgueMeasure.prod P))
    (hd4 : MemLp (FirstVariationDifferenceLpBounds.differenceCut D hbg hsg hb hs x y T v) 4
      (nonnegativeLebesgueMeasure.prod P)) :
    ‖sourceError D hbg hsg hb hs hnull x y T g hg hK hL v‖≤
      (M : ℝ)*(lpNorm (stateTimeCut (increment D hb hs x y T) T) 8 (nonnegativeLebesgueMeasure.prod P))^2*
        lpNorm (stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T v) T) 4 (nonnegativeLebesgueMeasure.prod P)+
      (L : ℝ)*lpNorm (FlowLinearizationLpBounds.remainderCut D hbg hsg hb hs x y T) 4 (nonnegativeLebesgueMeasure.prod P)*
        lpNorm (stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T v) T) 4 (nonnegativeLebesgueMeasure.prod P)+
      (L : ℝ)*lpNorm (stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T (y-x)) T) 4 (nonnegativeLebesgueMeasure.prod P)*
        lpNorm (FirstVariationDifferenceLpBounds.differenceCut D hbg hsg hb hs x y T v) 4 (nonnegativeLebesgueMeasure.prod P) := by
  have hy4 := (ConstructedFirstVariation.process_time_fourthMoment D hbg hsg hb hs y T hnull v).1
  have hx4 := (ConstructedFirstVariation.process_time_fourthMoment D hbg hsg hb hs x T hnull (y-x)).1
  have hh := LpProductBounds.lpNorm_three_products_le
    (sourceError D hbg hsg hb hs hnull x y T g hg hK hL v : TimeProcessL2 P)
    (Lp.memLp _) hi8 hy4 he4 hx4 hd4 M L M.coe_nonneg L.coe_nonneg
    (sourceError_bound D hbg hsg hb hs hnull x y T g hg hK hL hM v)
  change ‖(sourceError D hbg hsg hb hs hnull x y T g hg hK hL v : TimeProcessL2 P)‖≤_
  simpa only [Lp.norm_def,lpNorm] using hh
end Flow
end SphericalAging.SecondVariationSourceError
