module

public import SphericalAging.LinearResponseCoefficientDifference
public import SphericalAging.LpMomentBounds

public section

/-! Genuine spatial stability of first variations, using actual nonlinear
increment and first-response fourth moments and the same-driver resolvent. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.FirstVariationSpatialBounds
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment NonlinearIncrementFourthMoment
open PredictableLinearCoefficient StochasticLinearizationError LinearResolvent
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def fourthNormConstant (N : ℕ) (Kb Ks T : ℝ≥0) : ℝ :=
  (fourthConstant N Kb Ks T)^((1 : ℝ)/4)

lemma fourthNormConstant_nonneg (N : ℕ) (Kb Ks T : ℝ≥0) :
    0≤fourthNormConstant N Kb Ks T := Real.rpow_nonneg (fourthConstant_nonneg N Kb Ks T) _

theorem first_lpNorm_four_bound (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
    (x : State N) (T : ℝ≥0)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A) (v : State N) :
    lpNorm (stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T v) T) 4
      (nonnegativeLebesgueMeasure.prod P)≤fourthNormConstant N Kb Ks T*‖v‖ := by
  have hh := ConstructedFirstVariation.process_time_fourthMoment D hbg hsg hb hs x T hnull v
  apply LpMomentBounds.lpNorm_four_le_of_moment hh.1 (fourthConstant_nonneg N Kb Ks T)
  convert hh.2 using 1
  simp only [fourthConstant,momentConstant]
  ring

theorem increment_lpNorm_four_bound (D₀ : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
    (x y : State N) (T : ℝ≥0) (hT : 0<T) :
    lpNorm (stateTimeCut (increment (NullAugmentation.driver D₀) hb hs x y T) T) 4
      (nonnegativeLebesgueMeasure.prod P)≤fourthNormConstant N Kb Ks T*‖y-x‖ := by
  have hh := increment_fourthMoment D₀ hbg hsg hb hs x y T hT
  exact LpMomentBounds.lpNorm_four_le_of_moment hh.1 (fourthConstant_nonneg N Kb Ks T) hh.2

theorem response_difference_bound (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
    (hbd : ∀ i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀ i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (x : State N) (T : ℝ≥0) (hT : 0<T) :
    ∃ C : ℝ,0≤C ∧ ∀ y v : State N,
      ‖StochasticFlowDerivative.response (NullAugmentation.driver D₀) hbg hsg hb hs y T v-
        StochasticFlowDerivative.response (NullAugmentation.driver D₀) hbg hsg hb hs x T v‖≤
          C*‖y-x‖*‖v‖ := by
  let D := NullAugmentation.driver D₀
  let a := fun z => StochasticFlowDerivative.driftRows D hbg hb hs z T
  let sigma := fun z => StochasticFlowDerivative.noiseRows D hsg hb hs z T
  let L := sourceLinearMap D (a x) (sigma x) T
  let A := fourthNormConstant N Kb Ks T
  let C := ‖L‖*((N : ℝ)*T*Lb+(N : ℝ)^2*Real.sqrt T*Ls)*A^2
  have hA : 0≤A := fourthNormConstant_nonneg N Kb Ks T
  have hnull : ∀ B : Set Ω,MeasurableSet B → P B=0 → MeasurableSet[NullAugmentation.augment F P 0] B :=
    fun _ hm hzero => NullAugmentation.augment_null_known_zero F hm hzero
  have hC : 0≤C := by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  intro y v
  let U := StochasticFlowDerivative.response D hbg hsg hb hs y T v
  let rb := fun i => apply (a y i) U-apply (a x i) U
  let rs := fun i j => apply (sigma y i j) U-apply (sigma x i j) U
  have hd4 := increment_fourthMoment D₀ hbg hsg hb hs x y T hT
  have hy4 := ConstructedFirstVariation.process_time_fourthMoment D hbg hsg hb hs y T hnull v
  have hdn := increment_lpNorm_four_bound D₀ hbg hsg hb hs x y T hT
  have hyn := first_lpNorm_four_bound D hbg hsg hb hs y T hnull v
  have hrow {K M : ℝ≥0} {g : State N → ℝ} (hg : ContDiff ℝ ∞ g)
      (hK : LipschitzWith K g) (hM : LipschitzWith M (fderiv ℝ g)) :
      ‖apply (VariationalCoefficients.derivativeRow (GlobalSDE.horizonProcess D hb hs y T)
        (GlobalSDE.horizonProcess_stronglyAdapted D hb hs y T)
        (GlobalSDE.horizonProcess_continuous D hb hs y T) hg hK T) U-
      apply (VariationalCoefficients.derivativeRow (GlobalSDE.horizonProcess D hb hs x T)
        (GlobalSDE.horizonProcess_stronglyAdapted D hb hs x T)
        (GlobalSDE.horizonProcess_continuous D hb hs x T) hg hK T) U‖≤
          (M : ℝ)*A^2*‖y-x‖*‖v‖ := by
    have hp := PredictableProductNorm.norm_le_of_product _ _ _ hd4.1 hy4.1 M M.coe_nonneg
      (LinearResponseCoefficientDifference.derivative_apply_difference_bound hg hK hM _ _ _
        (GlobalSDE.horizonProcess_stronglyAdapted D hb hs x T)
        (GlobalSDE.horizonProcess_continuous D hb hs x T)
        (GlobalSDE.horizonProcess_stronglyAdapted D hb hs y T)
        (GlobalSDE.horizonProcess_continuous D hb hs y T) T U
        (ConstructedFirstVariation.process_timeCut D hbg hsg hb hs y T v))
    calc
      _ ≤ (M : ℝ)*lpNorm (stateTimeCut (increment D hb hs x y T) T) 4 (nonnegativeLebesgueMeasure.prod P)*
        lpNorm (stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T v) T) 4
          (nonnegativeLebesgueMeasure.prod P) := hp
      _ ≤ (M : ℝ)*(A*‖y-x‖)*(A*‖v‖) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hdn M.coe_nonneg) hyn lpNorm_nonneg (by positivity)
      _ = _ := by ring
  have hrb (i : Fin N) : ‖rb i‖≤(Lb : ℝ)*A^2*‖y-x‖*‖v‖ := hrow (hbg i) (hb i) (hbd i)
  have hrs (i j : Fin N) : ‖rs i j‖≤(Ls : ℝ)*A^2*‖y-x‖*‖v‖ := hrow (hsg i j) (hs i j) (hsd i j)
  have he := LinearResponseCoefficientDifference.same_source_difference D (a x) (a y)
    (sigma x) (sigma y) T (initialClass v T)
  change U-StochasticFlowDerivative.response D hbg hsg hb hs x T v=L (driftSource T rb+noiseSource D T rs) at he
  change ‖U-StochasticFlowDerivative.response D hbg hsg hb hs x T v‖≤_
  rw [he]
  calc
    _ ≤ ‖L‖*‖driftSource T rb+noiseSource D T rs‖ := L.le_opNorm _
    _ ≤ ‖L‖*(‖driftSource T rb‖+‖noiseSource D T rs‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg L)
    _ ≤ ‖L‖*((N : ℝ)*T*((Lb : ℝ)*A^2*‖y-x‖*‖v‖)+
      (N : ℝ)^2*Real.sqrt T*((Ls : ℝ)*A^2*‖y-x‖*‖v‖)) :=
      mul_le_mul_of_nonneg_left (add_le_add (driftSource_norm_le T rb _ hrb)
        (noiseSource_norm_le D T rs _ hrs)) (norm_nonneg L)
    _ = _ := by dsimp [C];ring

end SphericalAging.FirstVariationSpatialBounds
