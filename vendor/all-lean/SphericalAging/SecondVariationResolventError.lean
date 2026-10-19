module

public import SphericalAging.SecondVariationSourceError
public import SphericalAging.SecondVariationBilinear

public section
/-! Exact difference-minus-second-variation identity from the genuine
same-source Jacobian resolvents. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.SecondVariationResolventError
open HardSphereDynamics LocalSDE StochasticFlowDerivative PredictableLinearCoefficient
open LinearResolvent StochasticLinearizationError SecondVariationSourceError
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem response_remainder_eq (D : BrownianDriver N P F) {Kb Ks Lb Ls : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
    (hbd : ∀ i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀ i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
    (x y : State N) (T : ℝ≥0) (v : State N) :
    response D hbg hsg hb hs y T v-response D hbg hsg hb hs x T v-
      SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull x T (y-x) v=
    sourceLinearMap D (driftRows D hbg hb hs x T) (noiseRows D hsg hb hs x T) T
      (driftSource T (fun i => sourceError D hbg hsg hb hs hnull x y T (b i) (hbg i) (hb i) (hbd i) v)+
        noiseSource D T (fun i j => sourceError D hbg hsg hb hs hnull x y T (s i j) (hsg i j) (hs i j) (hsd i j) v)) := by
  let ax := driftRows D hbg hb hs x T
  let ay := driftRows D hbg hb hs y T
  let sx := noiseRows D hsg hb hs x T
  let sy := noiseRows D hsg hb hs y T
  let U := response D hbg hsg hb hs y T v
  let rb := fun i => apply (ay i) U-apply (ax i) U
  let rs := fun i j => apply (sy i j) U-apply (sx i j) U
  let Hb := SecondVariationalSDE.driftSource D hbg hsg hb hs hbd hnull x T (y-x) v
  let Hs := SecondVariationalSDE.noiseSource D hbg hsg hb hs hsd hnull x T (y-x) v
  let Eb := fun i => rb i-Hb i
  let Es := fun i j => rs i j-Hs i j
  let L := sourceLinearMap D ax sx T
  have he := LinearResponseCoefficientDifference.same_source_difference D ax ay sx sy T (initialClass v T)
  change response D hbg hsg hb hs y T v-response D hbg hsg hb hs x T v=L (driftSource T rb+noiseSource D T rs) at he
  have hsource : driftSource T Eb+noiseSource D T Es=
      driftSource T rb+noiseSource D T rs-(driftSource T Hb+noiseSource D T Hs) := by
    simp only [driftSource,noiseSource,Eb,Es,map_sub,Finset.sum_sub_distrib]
    abel
  change response D hbg hsg hb hs y T v-response D hbg hsg hb hs x T v-
    L (driftSource T Hb+noiseSource D T Hs)=L (driftSource T Eb+noiseSource D T Es)
  rw [he,←map_sub,hsource]
end SphericalAging.SecondVariationResolventError
