module

public import SphericalAging.FirstResponseSecondDerivative
public import SphericalAging.FlowTerminalDerivative

public section
/-! True differentiation of Jacobian coefficient rows along the actual flow. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.FirstCoefficientSecondDerivative
open HardSphereDynamics LocalSDE StochasticFlowDerivative PredictableLinearCoefficient
open SecondVariationSourceError FlowCoefficientDerivative TerminalLinearity
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
section Definition
variable (D : BrownianDriver N P F) {Kb Ks Lb Ls K L : ℝ≥0}
  {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
  (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
  (hbd : ∀ i,LipschitzWith Lb (fderiv ℝ (b i)))
  (hsd : ∀ i j,LipschitzWith Ls (fderiv ℝ (s i j)))
  (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
  (x : State N) (T : ℝ≥0) (g : State N → ℝ) (hg : ContDiff ℝ ∞ g)
  (hK : LipschitzWith K g) (hL : LipschitzWith L (fderiv ℝ g)) (v : State N)

@[expose] def rowSecondOperator : State N →L[ℝ] PredictableProcessL2 F P :=
  (coefficientOperator (row D hb hs T g hg hK x)).comp
    (SecondVariationBilinear.leftOperator D hbg hsg hb hs hbd hsd hnull x T v)+
  HessianInitialSource.leftOperator D hbg hsg hb hs hnull x T g hg hL v
end Definition

theorem firstCoefficient_hasFDerivAt_initial (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms K L M : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
    (hbd : ∀ i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀ i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (hbd2 : ∀ i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
    (hsd2 : ∀ i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
    (x : State N) (T : ℝ≥0) (hT : 0<T) (g : State N → ℝ) (hg : ContDiff ℝ ∞ g)
    (hK : LipschitzWith K g) (hL : LipschitzWith L (fderiv ℝ g))
    (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g))) (v : State N) :
    HasFDerivAt
      (fun y => apply (row (NullAugmentation.driver D₀) hb hs T g hg hK y)
        (response (NullAugmentation.driver D₀) hbg hsg hb hs y T v))
      (rowSecondOperator (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
        (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T g hg hK hL v) x := by
  let D := NullAugmentation.driver D₀
  have hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[NullAugmentation.augment F P 0] A :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  let Q := fun y => response D hbg hsg hb hs y T v
  let G := fun y => apply (row D hb hs T g hg hK y) (Q y)-apply (row D hb hs T g hg hK x) (Q y)
  have hG : HasFDerivAt G (HessianInitialSource.leftOperator D hbg hsg hb hs hnull x T g hg hL v) x := by
    obtain ⟨A,B,hA,hB,hbound⟩ := SecondVariationSourceRate.sourceError_rate D₀ hbg hsg hb hs hbd hsd x T hT
      g hg hK hL hM v
    have hh := SecondVariationPowerBounds.isLittleO_of_bound x hA hB hbound
    rw [hasFDerivAt_iff_isLittleO]
    simpa only [G,Q,sourceError,sub_self,sub_zero,HessianInitialSource.leftOperator_apply] using hh
  have hQ := FirstResponseSecondDerivative.response_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x T hT v
  have hh := ((coefficientOperator (row D hb hs T g hg hK x)).hasFDerivAt.comp x hQ).add hG
  convert hh using 1
  · funext y
    change apply (row D hb hs T g hg hK y) (Q y)=
      apply (row D hb hs T g hg hK x) (Q y)+(apply (row D hb hs T g hg hK y) (Q y)-apply (row D hb hs T g hg hK x) (Q y))
    abel
  · rfl
end SphericalAging.FirstCoefficientSecondDerivative
