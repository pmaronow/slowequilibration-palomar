module

public import SphericalAging.FlowLinearizationLpBounds

public section
/-! Actual spatial response differences in L⁴ from their L² stability and
constructed eighth moments. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.FirstVariationDifferenceLpBounds
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment StochasticFlowDerivative
open FlowVariationEighthMoment FlowLinearizationLpBounds
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
section Flow
variable (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
  {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
  (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
  (x y : State N) (T : ℝ≥0) (v : State N)

@[expose] def differenceCut : ℝ≥0 × Ω → State N := fun q =>
  stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T v) T q-
  stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T v) T q

theorem differenceCut_class_ae : differenceCut D hbg hsg hb hs x y T v
    =ᵐ[nonnegativeLebesgueMeasure.prod P]
      ((response D hbg hsg hb hs y T v-response D hbg hsg hb hs x T v : PredictableStateL2 N F P) :
        Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) := by
  have hx := ConstructedFirstVariation.process_timeCut D hbg hsg hb hs x T v
  have hy := ConstructedFirstVariation.process_timeCut D hbg hsg hb hs y T v
  have he := Lp.coeFn_sub (response D hbg hsg hb hs y T v : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
    (response D hbg hsg hb hs x T v)
  filter_upwards [hx,hy,he] with q hx hy he
  simp only [Submodule.coe_sub] at he ⊢
  rw [he,Pi.sub_apply]
  by_cases ht : q.1∈Ioc (0 : ℝ≥0) T
  · simp only [indicator_of_mem (show q∈Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨ht,mem_univ _⟩)] at hx hy
    simp only [differenceCut,stateTimeCut,ht,ite_true,hx,hy]
  · simp only [indicator_of_notMem (show q∉Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from by simp [ht])] at hx hy
    simp only [differenceCut,stateTimeCut,ht,ite_false,←hx,←hy,sub_self]

theorem differenceCut_memLp_two : MemLp (differenceCut D hbg hsg hb hs x y T v) 2
    (nonnegativeLebesgueMeasure.prod P) :=
  (Lp.memLp ((response D hbg hsg hb hs y T v-response D hbg hsg hb hs x T v : PredictableStateL2 N F P) :
    Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))).ae_eq
      (differenceCut_class_ae D hbg hsg hb hs x y T v).symm

theorem differenceCut_lpNorm_two : lpNorm (differenceCut D hbg hsg hb hs x y T v) 2
    (nonnegativeLebesgueMeasure.prod P)=‖response D hbg hsg hb hs y T v-response D hbg hsg hb hs x T v‖ := by
  change (eLpNorm _ 2 _).toReal=‖((response D hbg hsg hb hs y T v-response D hbg hsg hb hs x T v :
    PredictableStateL2 N F P) : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))‖
  rw [Lp.norm_def,eLpNorm_congr_ae (differenceCut_class_ae D hbg hsg hb hs x y T v)]
end Flow

theorem difference_four_bound (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
    (hbd : ∀ i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀ i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (x : State N) (T : ℝ≥0) (hT : 0<T) :
    ∃ C : ℝ,0≤C ∧ ∀ y v : State N,
      MemLp (differenceCut (NullAugmentation.driver D₀) hbg hsg hb hs x y T v) 4
        (nonnegativeLebesgueMeasure.prod P) ∧
      lpNorm (differenceCut (NullAugmentation.driver D₀) hbg hsg hb hs x y T v) 4
        (nonnegativeLebesgueMeasure.prod P)≤(C*‖y-x‖*‖v‖)^((1 : ℝ)/3)*
          (2*eighthNormConstant N Kb Ks T*‖v‖)^((2 : ℝ)/3) := by
  obtain ⟨C,hC,hbound⟩ := FirstVariationSpatialBounds.response_difference_bound D₀ hbg hsg hb hs hbd hsd x T hT
  refine ⟨C,hC,?_⟩
  intro y v
  let D := NullAugmentation.driver D₀
  have hnull : ∀ B : Set Ω,MeasurableSet B → P B=0 → MeasurableSet[NullAugmentation.augment F P 0] B :=
    fun _ hm hzero => NullAugmentation.augment_null_known_zero F hm hzero
  have hx := first_variation_time_eighthMoment D hbg hsg hb hs x T hnull v
  have hy := first_variation_time_eighthMoment D hbg hsg hb hs y T hnull v
  have he8 : MemLp (differenceCut D hbg hsg hb hs x y T v) 8 (nonnegativeLebesgueMeasure.prod P) := hy.1.sub hx.1
  have he2 := differenceCut_memLp_two D hbg hsg hb hs x y T v
  have hb2 : lpNorm (differenceCut D hbg hsg hb hs x y T v) 2
      (nonnegativeLebesgueMeasure.prod P)≤C*‖y-x‖*‖v‖ := by
    rw [differenceCut_lpNorm_two];exact hbound y v
  have hb8 : lpNorm (differenceCut D hbg hsg hb hs x y T v) 8
      (nonnegativeLebesgueMeasure.prod P)≤2*eighthNormConstant N Kb Ks T*‖v‖ := by
    have hnx := LpMomentBounds.lpNorm_eight_le_of_moment hx.1 (eighthConstant_nonneg N Kb Ks T) hx.2
    have hny := LpMomentBounds.lpNorm_eight_le_of_moment hy.1 (eighthConstant_nonneg N Kb Ks T) hy.2
    exact (lpNorm_sub_le hy.1 (by norm_num)).trans
      ((add_le_add hny hnx).trans_eq (by unfold eighthNormConstant;ring))
  refine ⟨LpEightInterpolation.memLp_four he2 he8,?_⟩
  exact (LpEightInterpolation.lpNorm_four_le he2 he8).trans (mul_le_mul
    (Real.rpow_le_rpow lpNorm_nonneg hb2 (by norm_num))
    (Real.rpow_le_rpow lpNorm_nonneg hb8 (by norm_num))
    (Real.rpow_nonneg lpNorm_nonneg _) (Real.rpow_nonneg (by positivity) _))
end SphericalAging.FirstVariationDifferenceLpBounds
