module

public import SphericalAging.HessianSourceContinuity
public import SphericalAging.FlowCoefficientApplicationContinuity
public import SphericalAging.LinearResponseSpatialContinuity
public import SphericalAging.SecondVariationBilinear
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

public section
/-! Constructed second variations and their bilinear operators are
spatially continuous; the proof uses actual sources and coefficients. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.SecondVariationContinuity
open HardSphereDynamics LocalSDE StochasticFlowDerivative StochasticLinearizationError VolterraLinearity
set_option maxHeartbeats 1800000
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
section Flow
variable (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms : ℝ≥0}
  {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
  (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
  (hbd : ∀ i,LipschitzWith Lb (fderiv ℝ (b i)))
  (hsd : ∀ i j,LipschitzWith Ls (fderiv ℝ (s i j)))
  (hbd2 : ∀ i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
  (hsd2 : ∀ i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
  (T : ℝ≥0) (hT : 0<T)
include hbd2 hsd2 hT

theorem responseClass_continuous (v w : State N) : Continuous
    (fun x => SecondVariationalSDE.responseClass (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T v w) := by
  classical
  let D := NullAugmentation.driver D₀
  have hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[NullAugmentation.augment F P 0] A :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  let R := fun x i => HessianInitialSource.source D hbg hsg hb hs hnull x T (b i) (hbg i) (hbd i) v w
  let S := fun x i j => HessianInitialSource.source D hbg hsg hb hs hnull x T (s i j) (hsg i j) (hsd i j) v w
  have hR (i : Fin N) : Continuous (fun x => R x i) :=
    HessianSourceContinuity.source_continuous D₀ hbg hsg hb hs hbd hsd T hT (b i) (hbg i) (hbd i) (hbd2 i) v w
  have hS (i j : Fin N) : Continuous (fun x => S x i j) :=
    HessianSourceContinuity.source_continuous D₀ hbg hsg hb hs hbd hsd T hT (s i j) (hsg i j) (hsd i j) (hsd2 i j) v w
  have hd : Continuous (fun x => driftSource T (R x)) := by
    apply continuous_finset_sum
    intro i _
    exact (stateInclusion i).continuous.comp ((driftOperator T).continuous.comp (hR i))
  have hn : Continuous (fun x => noiseSource D T (S x)) := by
    apply continuous_finset_sum
    intro i _
    apply (stateInclusion i).continuous.comp
    apply continuous_finset_sum
    intro j _
    exact (itoOperator (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) T).continuous.comp (hS i j)
  exact LinearResponseSpatialContinuity.sourceClass_continuous D T
    (fun x => driftRows D hbg hb hs x T) (fun x => noiseRows D hsg hb hs x T)
    (fun x => driftSource T (R x)+noiseSource D T (S x))
    (fun i Q => FlowCoefficientApplicationContinuity.apply_row_continuous D hb hs T (b i) (hbg i) (hb i) (hbd i) Q)
    (fun i j Q => FlowCoefficientApplicationContinuity.apply_row_continuous D hb hs T (s i j) (hsg i j) (hs i j) (hsd i j) Q)
    (hd.add hn)

theorem leftOperator_continuous (v : State N) : Continuous
    (fun x => SecondVariationBilinear.leftOperator (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T v) := by
  apply continuous_clm_apply.mpr
  intro w
  exact responseClass_continuous D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT w v

end Flow
end SphericalAging.SecondVariationContinuity
