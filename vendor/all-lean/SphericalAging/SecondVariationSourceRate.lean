module

public import SphericalAging.SecondVariationSourceError
public import SphericalAging.SecondVariationPowerBounds

public section
/-! Actual source remainders have quadratic plus four-thirds spatial rate. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.SecondVariationSourceRate
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment NonlinearIncrementFourthMoment
open FlowVariationEighthMoment FlowLinearizationLpBounds FirstVariationSpatialBounds
open SecondVariationSourceError SecondVariationPowerBounds
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem sourceError_rate (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls K L M : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
    (hbd : ∀ i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀ i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (x : State N) (T : ℝ≥0) (hT : 0<T) (g : State N → ℝ) (hg : ContDiff ℝ ∞ g)
    (hK : LipschitzWith K g) (hL : LipschitzWith L (fderiv ℝ g))
    (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g))) (v : State N) :
    ∃ A B : ℝ,0≤A ∧ 0≤B ∧ ∀ y : State N,
      ‖sourceError (NullAugmentation.driver D₀) hbg hsg hb hs
        (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x y T g hg hK hL v‖≤
          A*‖y-x‖^2+B*‖y-x‖^((4 : ℝ)/3) := by
  let D := NullAugmentation.driver D₀
  have hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[NullAugmentation.augment F P 0] A :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  obtain ⟨Ce,hCe,he⟩ := remainder_four_bound D₀ hbg hsg hb hs hbd hsd x T hT
  obtain ⟨Cy,hCy,hy⟩ := FirstVariationDifferenceLpBounds.difference_four_bound D₀ hbg hsg hb hs hbd hsd x T hT
  let Q := fourthNormConstant N Kb Ks T
  let Z := eighthNormConstant N Kb Ks T
  have hQ : 0≤Q := fourthNormConstant_nonneg N Kb Ks T
  have hZ : 0≤Z := Real.rpow_nonneg (eighthConstant_nonneg N Kb Ks T) _
  let E := Ce^((1 : ℝ)/3)*(2*Z)^((2 : ℝ)/3)
  let Y := Cy^((1 : ℝ)/3)*(2*Z)^((2 : ℝ)/3)
  have hE : 0≤E := mul_nonneg (Real.rpow_nonneg hCe _) (Real.rpow_nonneg (by positivity) _)
  have hY : 0≤Y := mul_nonneg (Real.rpow_nonneg hCy _) (Real.rpow_nonneg (by positivity) _)
  let A := (M : ℝ)*Z^2*Q*‖v‖
  let B := (L : ℝ)*E*Q*‖v‖+(L : ℝ)*Q*Y*‖v‖
  refine ⟨A,B,by dsimp [A];positivity,by dsimp [B];positivity,?_⟩
  intro y
  have hi := increment_time_eighthMoment D₀ hbg hsg hb hs x y T hT
  have hni : lpNorm (stateTimeCut (increment D hb hs x y T) T) 8
      (nonnegativeLebesgueMeasure.prod P)≤Z*‖y-x‖ :=
    LpMomentBounds.lpNorm_eight_le_of_moment hi.1 (eighthConstant_nonneg N Kb Ks T) hi.2
  have hny := first_lpNorm_four_bound D hbg hsg hb hs y T hnull v
  have hnx := first_lpNorm_four_bound D hbg hsg hb hs x T hnull (y-x)
  have hne : lpNorm (remainderCut D hbg hsg hb hs x y T) 4
      (nonnegativeLebesgueMeasure.prod P)≤E*‖y-x‖^((4 : ℝ)/3) := by
    have hh := (he y).2
    rw [flow_power Ce (2*Z) ‖y-x‖ hCe (by positivity) (norm_nonneg _)] at hh
    exact hh
  have hnd : lpNorm (FirstVariationDifferenceLpBounds.differenceCut D hbg hsg hb hs x y T v) 4
      (nonnegativeLebesgueMeasure.prod P)≤Y*‖y-x‖^((1 : ℝ)/3)*‖v‖ := by
    have hh := (hy y v).2
    rw [response_power Cy (2*Z) ‖y-x‖ ‖v‖ hCy (by positivity) (norm_nonneg _) (norm_nonneg _)] at hh
    exact hh
  have hp := sourceError_norm_le D hbg hsg hb hs hnull x y T g hg hK hL hM v hi.1 (he y).1 (hy y v).1
  apply hp.trans
  have ht1 := mul_le_mul
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ lpNorm_nonneg hni 2) M.coe_nonneg)
    hny lpNorm_nonneg (by positivity : 0≤(M : ℝ)*(Z*‖y-x‖)^2)
  have ht2 := mul_le_mul (mul_le_mul_of_nonneg_left hne L.coe_nonneg)
    hny lpNorm_nonneg (by positivity : 0≤(L : ℝ)*(E*‖y-x‖^((4 : ℝ)/3)))
  have ht3 := mul_le_mul (mul_le_mul_of_nonneg_left hnx L.coe_nonneg)
    hnd lpNorm_nonneg (by positivity : 0≤(L : ℝ)*(Q*‖y-x‖))
  apply (add_le_add (add_le_add ht1 ht2) ht3).trans_eq
  dsimp [A,B]
  have hr := norm_mul_third ‖y-x‖ (norm_nonneg _)
  calc
    _ = (M : ℝ)*Z^2*Q*‖v‖*‖y-x‖^2+(L : ℝ)*E*Q*‖v‖*‖y-x‖^((4 : ℝ)/3)+
        (L : ℝ)*Q*Y*‖v‖*(‖y-x‖*‖y-x‖^((1 : ℝ)/3)) := by ring
    _ = _ := by rw [hr];ring
end SphericalAging.SecondVariationSourceRate
