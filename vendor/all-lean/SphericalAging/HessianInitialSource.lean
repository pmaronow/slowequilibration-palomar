module

public import SphericalAging.FirstVariationLpLift
public import SphericalAging.PredictableProductNorm

public section
/-! Genuine quadratic Hessian forcing as a continuous bilinear function
of initial directions. Linearity uses the actual first response identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.HessianInitialSource
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
section Flow
variable (D : BrownianDriver N P F) {Kb Ks L : ℝ≥0}
  {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
  (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
  (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
  (x : State N) (T : ℝ≥0) (g : State N → ℝ) (hg : ContDiff ℝ ∞ g)
  (hL : LipschitzWith L (fderiv ℝ g))

@[expose] def source (v w : State N) : PredictableProcessL2 F P :=
  HessianQuadraticSource.source g hg hL (GlobalSDE.horizonProcess D hb hs x T)
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

theorem source_coe (v w : State N) : (source D hbg hsg hb hs hnull x T g hg hL v w : TimeProcessL2 P)
    =ᵐ[nonnegativeLebesgueMeasure.prod P] FourPapersCommon.continuousAdaptedTimeCut
      (HessianQuadraticSource.hessianField g (GlobalSDE.horizonProcess D hb hs x T)
        (ConstructedFirstVariation.process D hbg hsg hb hs x T v)
        (ConstructedFirstVariation.process D hbg hsg hb hs x T w)) T :=
  HessianQuadraticSource.source_coe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem source_add_left (v w z : State N) :
    source D hbg hsg hb hs hnull x T g hg hL (v+z) w=source D hbg hsg hb hs hnull x T g hg hL v w+source D hbg hsg hb hs hnull x T g hg hL z w := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [source_coe D hbg hsg hb hs hnull x T g hg hL (v+z) w,source_coe D hbg hsg hb hs hnull x T g hg hL v w,
    source_coe D hbg hsg hb hs hnull x T g hg hL z w,
    FirstVariationLpLift.timeCut_add D hbg hsg hb hs x T v z,Lp.coeFn_add (source D hbg hsg hb hs hnull x T g hg hL v w : TimeProcessL2 P) (source D hbg hsg hb hs hnull x T g hg hL z w)]
    with q hsourceA hsourceB hsourceC ht hsum
  change (source D hbg hsg hb hs hnull x T g hg hL (v+z) w : TimeProcessL2 P) q=((source D hbg hsg hb hs hnull x T g hg hL v w : TimeProcessL2 P)+(source D hbg hsg hb hs hnull x T g hg hL z w : TimeProcessL2 P)) q
  rw [hsum,Pi.add_apply,hsourceA,hsourceB,hsourceC]
  by_cases hq : q.1∈Ioc (0 : ℝ≥0) T
  · simp only [stateTimeCut,hq,ite_true] at ht
    simp only [FourPapersCommon.continuousAdaptedTimeCut,hq,ite_true]
    simp only [HessianQuadraticSource.hessianField,map_add,ContinuousLinearMap.add_apply,ht]
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,hq,ite_false,zero_add]

theorem source_smul_left (c : ℝ) (v w : State N) :
    source D hbg hsg hb hs hnull x T g hg hL (c • v) w=c • source D hbg hsg hb hs hnull x T g hg hL v w := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [source_coe D hbg hsg hb hs hnull x T g hg hL (c • v) w,source_coe D hbg hsg hb hs hnull x T g hg hL v w,
    
    FirstVariationLpLift.timeCut_smul D hbg hsg hb hs x T c v,Lp.coeFn_smul c (source D hbg hsg hb hs hnull x T g hg hL v w : TimeProcessL2 P)]
    with q hsourceA hsourceB ht hsum
  change (source D hbg hsg hb hs hnull x T g hg hL (c • v) w : TimeProcessL2 P) q=(c • (source D hbg hsg hb hs hnull x T g hg hL v w : TimeProcessL2 P)) q
  rw [hsum,Pi.smul_apply,hsourceA,hsourceB]
  by_cases hq : q.1∈Ioc (0 : ℝ≥0) T
  · simp only [stateTimeCut,hq,ite_true] at ht
    simp only [FourPapersCommon.continuousAdaptedTimeCut,hq,ite_true]
    simp only [HessianQuadraticSource.hessianField,map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul,ht]
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,hq,ite_false,smul_zero]

theorem source_add_right (v w z : State N) :
    source D hbg hsg hb hs hnull x T g hg hL v (w+z)=source D hbg hsg hb hs hnull x T g hg hL v w+source D hbg hsg hb hs hnull x T g hg hL v z := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [source_coe D hbg hsg hb hs hnull x T g hg hL v (w+z),source_coe D hbg hsg hb hs hnull x T g hg hL v w,
    source_coe D hbg hsg hb hs hnull x T g hg hL v z,
    FirstVariationLpLift.timeCut_add D hbg hsg hb hs x T w z,Lp.coeFn_add (source D hbg hsg hb hs hnull x T g hg hL v w : TimeProcessL2 P) (source D hbg hsg hb hs hnull x T g hg hL v z)]
    with q hsourceA hsourceB hsourceC ht hsum
  change (source D hbg hsg hb hs hnull x T g hg hL v (w+z) : TimeProcessL2 P) q=((source D hbg hsg hb hs hnull x T g hg hL v w : TimeProcessL2 P)+(source D hbg hsg hb hs hnull x T g hg hL v z : TimeProcessL2 P)) q
  rw [hsum,Pi.add_apply,hsourceA,hsourceB,hsourceC]
  by_cases hq : q.1∈Ioc (0 : ℝ≥0) T
  · simp only [stateTimeCut,hq,ite_true] at ht
    simp only [FourPapersCommon.continuousAdaptedTimeCut,hq,ite_true]
    simp only [HessianQuadraticSource.hessianField,map_add,ht]
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,hq,ite_false,zero_add]

theorem source_smul_right (c : ℝ) (v w : State N) :
    source D hbg hsg hb hs hnull x T g hg hL v (c • w)=c • source D hbg hsg hb hs hnull x T g hg hL v w := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [source_coe D hbg hsg hb hs hnull x T g hg hL v (c • w),source_coe D hbg hsg hb hs hnull x T g hg hL v w,
    
    FirstVariationLpLift.timeCut_smul D hbg hsg hb hs x T c w,Lp.coeFn_smul c (source D hbg hsg hb hs hnull x T g hg hL v w : TimeProcessL2 P)]
    with q hsourceA hsourceB ht hsum
  change (source D hbg hsg hb hs hnull x T g hg hL v (c • w) : TimeProcessL2 P) q=(c • (source D hbg hsg hb hs hnull x T g hg hL v w : TimeProcessL2 P)) q
  rw [hsum,Pi.smul_apply,hsourceA,hsourceB]
  by_cases hq : q.1∈Ioc (0 : ℝ≥0) T
  · simp only [stateTimeCut,hq,ite_true] at ht
    simp only [FourPapersCommon.continuousAdaptedTimeCut,hq,ite_true]
    simp only [HessianQuadraticSource.hessianField,map_smul,smul_eq_mul,ht]
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,hq,ite_false,smul_zero]

@[expose] def leftLinearMap (w : State N) : State N →ₗ[ℝ] PredictableProcessL2 F P where
  toFun := fun v => source D hbg hsg hb hs hnull x T g hg hL v w
  map_add' v z := source_add_left D hbg hsg hb hs hnull x T g hg hL v w z
  map_smul' c v := source_smul_left D hbg hsg hb hs hnull x T g hg hL c v w

@[expose] def leftOperator (w : State N) : State N →L[ℝ] PredictableProcessL2 F P :=
  (leftLinearMap D hbg hsg hb hs hnull x T g hg hL w).toContinuousLinearMap

@[simp] theorem leftOperator_apply (v w : State N) :
    leftOperator D hbg hsg hb hs hnull x T g hg hL w v=source D hbg hsg hb hs hnull x T g hg hL v w := rfl

@[expose] def bilinearLinearMap : State N →ₗ[ℝ] (State N →L[ℝ] PredictableProcessL2 F P) where
  toFun := leftOperator D hbg hsg hb hs hnull x T g hg hL
  map_add' w z := by
    apply ContinuousLinearMap.ext
    intro v
    change source D hbg hsg hb hs hnull x T g hg hL v (w+z)=_
    exact source_add_right D hbg hsg hb hs hnull x T g hg hL v w z
  map_smul' c w := by
    apply ContinuousLinearMap.ext
    intro v
    change source D hbg hsg hb hs hnull x T g hg hL v (c • w)=_
    exact source_smul_right D hbg hsg hb hs hnull x T g hg hL c v w

@[expose] def bilinearOperator : State N →L[ℝ] State N →L[ℝ] PredictableProcessL2 F P :=
  LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := State N)
    (F' := State N →L[ℝ] PredictableProcessL2 F P)
    (bilinearLinearMap D hbg hsg hb hs hnull x T g hg hL)

@[simp] theorem bilinearOperator_apply (v w : State N) :
    bilinearOperator D hbg hsg hb hs hnull x T g hg hL w v=source D hbg hsg hb hs hnull x T g hg hL v w := rfl

end Flow
end SphericalAging.HessianInitialSource
