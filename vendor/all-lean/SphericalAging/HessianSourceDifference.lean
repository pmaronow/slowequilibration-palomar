module

public import SphericalAging.LpThreeProductBounds
public import SphericalAging.FirstVariationLpContinuity
public import SphericalAging.HessianInitialSource

public section
/-! Genuine Hessian-source continuity estimates along constructed flows. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.HessianSourceDifference
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment NonlinearIncrementFourthMoment
open FirstVariationDifferenceLpBounds FlowVariationEighthMoment
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem hessian_difference_bound {g : State N → ℝ} {L M : ℝ≥0}
    (hL : LipschitzWith L (fderiv ℝ g))
    (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g))) (x y a b c d : State N) :
    ‖fderiv ℝ (fderiv ℝ g) y a b-fderiv ℝ (fderiv ℝ g) x c d‖≤
      (M : ℝ)*‖y-x‖*‖a‖*‖b‖+(L : ℝ)*‖a-c‖*‖b‖+(L : ℝ)*‖c‖*‖b-d‖ := by
  let Hx := fderiv ℝ (fderiv ℝ g) x
  let Hy := fderiv ℝ (fderiv ℝ g) y
  have he : Hy a b-Hx c d=(Hy-Hx) a b+Hx (a-c) b+Hx c (b-d) := by
    simp only [map_sub,ContinuousLinearMap.sub_apply];ring
  rw [he]
  have hH (u z : State N) : ‖Hx u z‖≤(L : ℝ)*‖u‖*‖z‖ :=
    ((Hx u).le_opNorm z).trans (mul_le_mul_of_nonneg_right
      (Hx.le_of_opNorm_le (norm_fderiv_le_of_lipschitz ℝ hL) u) (norm_nonneg _))
  have hd : ‖Hy-Hx‖≤(M : ℝ)*‖y-x‖ := by simpa only [dist_eq_norm] using hM.dist_le_mul y x
  have ht : ‖(Hy-Hx) a b‖≤(M : ℝ)*‖y-x‖*‖a‖*‖b‖ :=
    (((Hy-Hx) a).le_opNorm b).trans (mul_le_mul_of_nonneg_right
      ((Hy-Hx).le_of_opNorm_le hd a) (norm_nonneg _))
  calc
    _ ≤ ‖(Hy-Hx) a b+Hx (a-c) b‖+‖Hx c (b-d)‖ := norm_add_le _ _
    _ ≤ ‖(Hy-Hx) a b‖+‖Hx (a-c) b‖+‖Hx c (b-d)‖ := add_le_add (norm_add_le _ _) (le_refl _)
    _ ≤ _ := add_le_add (add_le_add ht (hH (a-c) b)) (hH c (b-d))

section Fields
variable (D : BrownianDriver N P F) {Kb Ks L M : ℝ≥0}
  {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
  (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
  (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
  (x y : State N) (T : ℝ≥0) (g : State N → ℝ) (hg : ContDiff ℝ ∞ g)
  (hL : LipschitzWith L (fderiv ℝ g)) (v w : State N)

theorem source_difference_bound (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g))) :
    ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      ‖((HessianInitialSource.source D hbg hsg hb hs hnull y T g hg hL v w-
        HessianInitialSource.source D hbg hsg hb hs hnull x T g hg hL v w : PredictableProcessL2 F P) : TimeProcessL2 P) q‖≤
      (M : ℝ)*‖stateTimeCut (increment D hb hs x y T) T q‖*
        ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T v) T q‖*
        ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T w) T q‖+
      (L : ℝ)*‖differenceCut D hbg hsg hb hs x y T v q‖*
        ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T w) T q‖+
      (L : ℝ)*‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T v) T q‖*
        ‖differenceCut D hbg hsg hb hs x y T w q‖ := by
  filter_upwards [Lp.coeFn_sub
      (HessianInitialSource.source D hbg hsg hb hs hnull y T g hg hL v w : TimeProcessL2 P)
      (HessianInitialSource.source D hbg hsg hb hs hnull x T g hg hL v w),
    HessianInitialSource.source_coe D hbg hsg hb hs hnull x T g hg hL v w,
    HessianInitialSource.source_coe D hbg hsg hb hs hnull y T g hg hL v w] with q he hx hy
  change ‖((HessianInitialSource.source D hbg hsg hb hs hnull y T g hg hL v w : TimeProcessL2 P)-
    (HessianInitialSource.source D hbg hsg hb hs hnull x T g hg hL v w : TimeProcessL2 P)) q‖≤_
  rw [he,Pi.sub_apply,hx,hy]
  by_cases ht : q.1∈Ioc (0 : ℝ≥0) T
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,HessianQuadraticSource.hessianField,
      stateTimeCut,increment,differenceCut,ht,ite_true]
    exact hessian_difference_bound hL hM _ _ _ _ _ _
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,stateTimeCut,differenceCut,ht,ite_false,
      sub_self,norm_zero,mul_zero,add_zero,le_refl]
end Fields
end SphericalAging.HessianSourceDifference
