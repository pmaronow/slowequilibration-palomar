module

public import SphericalAging.HessianSourceNorm

public section
/-! Actual Hessian quadratic sources are spatially continuous in L². -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.HessianSourceContinuity
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment NonlinearIncrementFourthMoment
open FirstVariationDifferenceLpBounds FlowVariationEighthMoment FlowLinearizationLpBounds FirstVariationSpatialBounds
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem source_continuous (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls L M : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
    (hbd : ∀ i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀ i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (T : ℝ≥0) (hT : 0<T) (g : State N → ℝ) (hg : ContDiff ℝ ∞ g)
    (hL : LipschitzWith L (fderiv ℝ g)) (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g)))
    (v w : State N) : Continuous (fun x => HessianInitialSource.source (NullAugmentation.driver D₀) hbg hsg hb hs
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T g hg hL v w) := by
  let D := NullAugmentation.driver D₀
  have hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[NullAugmentation.augment F P 0] A :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  let Q := fourthNormConstant N Kb Ks T
  let Z := eighthNormConstant N Kb Ks T
  have hQ : 0≤Q := fourthNormConstant_nonneg N Kb Ks T
  have hZ : 0≤Z := Real.rpow_nonneg (eighthConstant_nonneg N Kb Ks T) _
  let S := fun x => HessianInitialSource.source D hbg hsg hb hs hnull x T g hg hL v w
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨C,hC,hd⟩ := difference_four_bound D₀ hbg hsg hb hs hbd hsd x T hT
  let DV := fun y => lpNorm (differenceCut D hbg hsg hb hs x y T v) 4 (nonnegativeLebesgueMeasure.prod P)
  let DW := fun y => lpNorm (differenceCut D hbg hsg hb hs x y T w) 4 (nonnegativeLebesgueMeasure.prod P)
  let A := (M : ℝ)*Q*Z^2*‖v‖*‖w‖
  let B := (L : ℝ)*Q*‖w‖
  let C := (L : ℝ)*Q*‖v‖
  have hbound (y : State N) : ‖S y-S x‖≤A*‖y-x‖+B*DV y+C*DW y := by
    have hi := increment_fourthMoment D₀ hbg hsg hb hs x y T hT
    have hv := first_variation_time_eighthMoment D hbg hsg hb hs y T hnull v
    have hw := first_variation_time_eighthMoment D hbg hsg hb hs y T hnull w
    have hni := increment_lpNorm_four_bound D₀ hbg hsg hb hs x y T hT
    have hnv := LpMomentBounds.lpNorm_eight_le_of_moment hv.1 (eighthConstant_nonneg N Kb Ks T) hv.2
    have hnw := LpMomentBounds.lpNorm_eight_le_of_moment hw.1 (eighthConstant_nonneg N Kb Ks T) hw.2
    have hnx := first_lpNorm_four_bound D hbg hsg hb hs x T hnull v
    have hny := first_lpNorm_four_bound D hbg hsg hb hs y T hnull w
    have hp := HessianSourceNorm.source_difference_norm_le D hbg hsg hb hs hnull x y T g hg hL hM v w
      hi.1 hv.1 hw.1 (hd y v).1 (hd y w).1
    apply hp.trans
    calc
      _ ≤ (M : ℝ)*(Q*‖y-x‖)*(Z*‖v‖)*(Z*‖w‖)+
          (L : ℝ)*DV y*(Q*‖w‖)+(L : ℝ)*(Q*‖v‖)*DW y := by
        dsimp only [DV,DW]
        gcongr <;> first | exact lpNorm_nonneg | exact hnv | exact hnw | exact mul_nonneg L.coe_nonneg lpNorm_nonneg
      _ = _ := by dsimp [A,B,C];ring
  have hDV := FirstVariationLpContinuity.differenceCut_lpNorm_four_tendsto_zero D₀ hbg hsg hb hs hbd hsd x T hT v
  have hDW := FirstVariationLpContinuity.differenceCut_lpNorm_four_tendsto_zero D₀ hbg hsg hb hs hbd hsd x T hT w
  have hn : Tendsto (fun y : State N => ‖y-x‖) (𝓝 x) (𝓝 0) := by
    have hc : Continuous (fun y : State N => ‖y-x‖) := (continuous_id.sub continuous_const).norm
    simpa only [sub_self,norm_zero] using hc.tendsto x
  have ht : Tendsto (fun y => A*‖y-x‖+B*DV y+C*DW y) (𝓝 x) (𝓝 0) := by
    simpa only [mul_zero,zero_add] using ((hn.const_mul A).add (hDV.const_mul B)).add (hDW.const_mul C)
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) hbound ht
end SphericalAging.HessianSourceContinuity
