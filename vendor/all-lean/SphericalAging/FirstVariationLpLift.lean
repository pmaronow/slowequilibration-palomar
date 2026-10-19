module

public import SphericalAging.FlowVariationEighthMoment
public import SphericalAging.LpEightInterpolation
public import Mathlib.Analysis.Normed.Module.FiniteDimension

public section

/-! The genuine first variational solution lifted to L⁴ and L⁸. Its
linearity follows from the actual predictable L² response identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.FirstVariationLpLift
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
local instance : Fact ((1 : ℝ≥0∞)≤4) := ⟨by norm_num⟩
local instance : Fact ((1 : ℝ≥0∞)≤8) := ⟨by norm_num⟩
section Flow
variable (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
  {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
  (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
  (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
  (x : State N) (T : ℝ≥0)

@[expose] def fourthClass (v : State N) : Lp (State N) 4 (nonnegativeLebesgueMeasure.prod P) :=
  (ConstructedFirstVariation.process_time_fourthMoment D hbg hsg hb hs x T hnull v).1.toLp _

@[expose] def eighthClass (v : State N) : Lp (State N) 8 (nonnegativeLebesgueMeasure.prod P) :=
  (FlowVariationEighthMoment.first_variation_time_eighthMoment D hbg hsg hb hs x T hnull v).1.toLp _

theorem fourthClass_ae (v : State N) : fourthClass D hbg hsg hb hs hnull x T v
    =ᵐ[nonnegativeLebesgueMeasure.prod P] stateTimeCut
      (ConstructedFirstVariation.process D hbg hsg hb hs x T v) T :=
  (ConstructedFirstVariation.process_time_fourthMoment D hbg hsg hb hs x T hnull v).1.coeFn_toLp

theorem eighthClass_ae (v : State N) : eighthClass D hbg hsg hb hs hnull x T v
    =ᵐ[nonnegativeLebesgueMeasure.prod P] stateTimeCut
      (ConstructedFirstVariation.process D hbg hsg hb hs x T v) T :=
  (FlowVariationEighthMoment.first_variation_time_eighthMoment D hbg hsg hb hs x T hnull v).1.coeFn_toLp

theorem timeCut_add (v w : State N) :
    stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T (v+w)) T
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        (fun q => stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T v) T q+
          stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T w) T q) := by
  have hc (u : State N) : stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T u) T
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        (StochasticFlowDerivative.response D hbg hsg hb hs x T u : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) := by
    rw [stateTimeCut_eq_indicator]
    exact ConstructedFirstVariation.process_timeCut D hbg hsg hb hs x T u
  have he : (StochasticFlowDerivative.response D hbg hsg hb hs x T (v+w) :
      Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))=
      (StochasticFlowDerivative.response D hbg hsg hb hs x T v : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))+
      (StochasticFlowDerivative.response D hbg hsg hb hs x T w : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) :=
    congrArg Subtype.val (map_add (StochasticFlowDerivative.response D hbg hsg hb hs x T) v w)
  filter_upwards [hc (v+w),hc v,hc w,Lp.coeFn_add
    (StochasticFlowDerivative.response D hbg hsg hb hs x T v : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
    (StochasticFlowDerivative.response D hbg hsg hb hs x T w : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))]
    with q hva hv hw hadd
  rw [hva,he,hadd,Pi.add_apply,← hv,← hw]

theorem timeCut_smul (c : ℝ) (v : State N) :
    stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T (c • v)) T
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        (fun q => c • stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T v) T q) := by
  have hc (u : State N) : stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T u) T
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        (StochasticFlowDerivative.response D hbg hsg hb hs x T u : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) := by
    rw [stateTimeCut_eq_indicator]
    exact ConstructedFirstVariation.process_timeCut D hbg hsg hb hs x T u
  have he : (StochasticFlowDerivative.response D hbg hsg hb hs x T (c • v) :
      Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))=
      c • (StochasticFlowDerivative.response D hbg hsg hb hs x T v : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) :=
    congrArg Subtype.val (map_smul (StochasticFlowDerivative.response D hbg hsg hb hs x T) c v)
  filter_upwards [hc (c • v),hc v,Lp.coeFn_smul c
    (StochasticFlowDerivative.response D hbg hsg hb hs x T v : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))]
    with q hcv hv hsmul
  rw [hcv,he,hsmul,Pi.smul_apply,← hv]

@[expose] def fourthLinearMap : State N →ₗ[ℝ] Lp (State N) 4 (nonnegativeLebesgueMeasure.prod P) where
  toFun := fourthClass D hbg hsg hb hs hnull x T
  map_add' v w := by
    apply Lp.ext
    filter_upwards [fourthClass_ae D hbg hsg hb hs hnull x T (v+w),
      fourthClass_ae D hbg hsg hb hs hnull x T v,fourthClass_ae D hbg hsg hb hs hnull x T w,
      timeCut_add D hbg hsg hb hs x T v w,Lp.coeFn_add
        (fourthClass D hbg hsg hb hs hnull x T v) (fourthClass D hbg hsg hb hs hnull x T w)]
      with q hva hv hw ha hs
    rw [hva,ha,← hv,← hw,hs,Pi.add_apply]
  map_smul' c v := by
    change fourthClass D hbg hsg hb hs hnull x T (c • v)=c • fourthClass D hbg hsg hb hs hnull x T v
    apply Lp.ext
    filter_upwards [fourthClass_ae D hbg hsg hb hs hnull x T (c • v),
      fourthClass_ae D hbg hsg hb hs hnull x T v,timeCut_smul D hbg hsg hb hs x T c v,
      Lp.coeFn_smul c (fourthClass D hbg hsg hb hs hnull x T v)] with q hcv hv hc hs
    rw [hcv,hc,← hv,hs,Pi.smul_apply]

@[expose] def fourthOperator : State N →L[ℝ] Lp (State N) 4 (nonnegativeLebesgueMeasure.prod P) :=
  (fourthLinearMap D hbg hsg hb hs hnull x T).toContinuousLinearMap

@[simp] theorem fourthOperator_apply (v : State N) :
    fourthOperator D hbg hsg hb hs hnull x T v=fourthClass D hbg hsg hb hs hnull x T v := rfl

end Flow
end SphericalAging.FirstVariationLpLift
