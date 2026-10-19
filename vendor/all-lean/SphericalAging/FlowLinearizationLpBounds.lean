module

public import SphericalAging.FirstVariationSpatialBounds
public import SphericalAging.FlowVariationEighthMoment

public section
/-! Actual flow linearization remainders in L⁴, proved from L² Taylor
errors and genuine eighth moments. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.FlowLinearizationLpBounds
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment NonlinearIncrementFourthMoment
open FlowVariationEighthMoment StochasticFlowDerivative
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
section Flow
variable (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
  {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
  (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
  (x y : State N) (T : ℝ≥0)

@[expose] def remainderCut : ℝ≥0 × Ω → State N :=
  fun q => stateTimeCut (increment D hb hs x y T) T q-
    stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T (y-x)) T q

theorem remainderCut_class_ae : remainderCut D hbg hsg hb hs x y T
    =ᵐ[nonnegativeLebesgueMeasure.prod P]
      ((GlobalSDE.horizonClass D hb hs y T-GlobalSDE.horizonClass D hb hs x T-
        response D hbg hsg hb hs x T (y-x) : PredictableStateL2 N F P) :
          Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) := by
  have hx := GlobalSDE.horizonProcess_timeCut D hb hs x T
  have hy := GlobalSDE.horizonProcess_timeCut D hb hs y T
  have hv := ConstructedFirstVariation.process_timeCut D hbg hsg hb hs x T (y-x)
  have hsub := Lp.coeFn_sub
    ((GlobalSDE.horizonClass D hb hs y T-GlobalSDE.horizonClass D hb hs x T : PredictableStateL2 N F P) :
      Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) (response D hbg hsg hb hs x T (y-x))
  have hsub' := Lp.coeFn_sub
    (GlobalSDE.horizonClass D hb hs y T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
    (GlobalSDE.horizonClass D hb hs x T)
  filter_upwards [hx,hy,hv,hsub,hsub'] with q hx hy hv hsub hsub'
  simp only [Submodule.coe_sub] at hsub ⊢
  rw [hsub,Pi.sub_apply,hsub',Pi.sub_apply]
  by_cases ht : q.1∈Ioc (0 : ℝ≥0) T
  · simp only [indicator_of_mem (show q∈Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨ht,mem_univ _⟩)] at hx hy hv
    simp only [remainderCut,stateTimeCut,ht,ite_true,increment,hx,hy,hv]
  · simp only [indicator_of_notMem (show q∉Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from by simp [ht])] at hx hy hv
    simp only [remainderCut,stateTimeCut,ht,ite_false,← hx,← hy,← hv,sub_self]

theorem remainderCut_memLp_two : MemLp (remainderCut D hbg hsg hb hs x y T) 2
    (nonnegativeLebesgueMeasure.prod P) :=
  (Lp.memLp ((GlobalSDE.horizonClass D hb hs y T-GlobalSDE.horizonClass D hb hs x T-
    response D hbg hsg hb hs x T (y-x) : PredictableStateL2 N F P) :
      Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))).ae_eq (remainderCut_class_ae D hbg hsg hb hs x y T).symm

theorem remainderCut_lpNorm_two : lpNorm (remainderCut D hbg hsg hb hs x y T) 2
    (nonnegativeLebesgueMeasure.prod P)=
      ‖GlobalSDE.horizonClass D hb hs y T-GlobalSDE.horizonClass D hb hs x T-
        response D hbg hsg hb hs x T (y-x)‖ := by
  change (eLpNorm _ 2 _).toReal=‖((GlobalSDE.horizonClass D hb hs y T-GlobalSDE.horizonClass D hb hs x T-
    response D hbg hsg hb hs x T (y-x) : PredictableStateL2 N F P) : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))‖
  rw [Lp.norm_def,eLpNorm_congr_ae (remainderCut_class_ae D hbg hsg hb hs x y T)]

end Flow

@[expose] def eighthNormConstant (N : ℕ) (Kb Ks T : ℝ≥0) : ℝ :=
  (eighthConstant N Kb Ks T)^((1 : ℝ)/8)

theorem remainder_four_bound (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
    (hbd : ∀ i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀ i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (x : State N) (T : ℝ≥0) (hT : 0<T) :
    ∃ C : ℝ,0≤C ∧ ∀ y : State N,
      MemLp (remainderCut (NullAugmentation.driver D₀) hbg hsg hb hs x y T) 4
        (nonnegativeLebesgueMeasure.prod P) ∧
      lpNorm (remainderCut (NullAugmentation.driver D₀) hbg hsg hb hs x y T) 4
        (nonnegativeLebesgueMeasure.prod P)≤(C*‖y-x‖^2)^((1 : ℝ)/3)*
          (2*eighthNormConstant N Kb Ks T*‖y-x‖)^((2 : ℝ)/3) := by
  obtain ⟨C,hC,hbound⟩ := quadratic_error_bound D₀ hbg hsg hb hs hbd hsd x T hT
  refine ⟨C,hC,?_⟩
  intro y
  let D := NullAugmentation.driver D₀
  have hnull : ∀ B : Set Ω,MeasurableSet B → P B=0 → MeasurableSet[NullAugmentation.augment F P 0] B :=
    fun _ hm hzero => NullAugmentation.augment_null_known_zero F hm hzero
  have hi := increment_time_eighthMoment D₀ hbg hsg hb hs x y T hT
  have hv := first_variation_time_eighthMoment D hbg hsg hb hs x T hnull (y-x)
  have he8 : MemLp (remainderCut D hbg hsg hb hs x y T) 8 (nonnegativeLebesgueMeasure.prod P) := hi.1.sub hv.1
  have he2 := remainderCut_memLp_two D hbg hsg hb hs x y T
  have hb2 : lpNorm (remainderCut D hbg hsg hb hs x y T) 2
      (nonnegativeLebesgueMeasure.prod P)≤C*‖y-x‖^2 := by
    rw [remainderCut_lpNorm_two]
    exact hbound y
  have hb8 : lpNorm (remainderCut D hbg hsg hb hs x y T) 8
      (nonnegativeLebesgueMeasure.prod P)≤2*eighthNormConstant N Kb Ks T*‖y-x‖ := by
    have hni := LpMomentBounds.lpNorm_eight_le_of_moment hi.1 (eighthConstant_nonneg N Kb Ks T) hi.2
    have hnv := LpMomentBounds.lpNorm_eight_le_of_moment hv.1 (eighthConstant_nonneg N Kb Ks T) hv.2
    exact (lpNorm_sub_le hi.1 (by norm_num)).trans ((add_le_add hni hnv).trans_eq (by unfold eighthNormConstant;ring))
  refine ⟨LpEightInterpolation.memLp_four he2 he8,?_⟩
  exact LpMomentBounds.fourth_remainder_bound he2 he8 hC (by
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (eighthConstant_nonneg N Kb Ks T) _)) hb2 hb8

end SphericalAging.FlowLinearizationLpBounds
