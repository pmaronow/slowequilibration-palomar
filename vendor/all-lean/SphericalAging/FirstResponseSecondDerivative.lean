module

public import SphericalAging.SecondVariationResolventError
public import SphericalAging.SecondVariationSourceRate
public import Mathlib.Analysis.Normed.Operator.Asymptotics

public section
/-! The genuine Fréchet derivative of each actual first response is the
constructed second variational strong SDE class. No derivative identity
is an input. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.FirstResponseSecondDerivative
open HardSphereDynamics LocalSDE StochasticFlowDerivative LinearResolvent
open StochasticLinearizationError SecondVariationSourceError VolterraLinearity
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem response_hasFDerivAt_initial (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
    (hbd : ∀ i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀ i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (hbd2 : ∀ i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
    (hsd2 : ∀ i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
    (x : State N) (T : ℝ≥0) (hT : 0<T) (v : State N) :
    HasFDerivAt (fun y => response (NullAugmentation.driver D₀) hbg hsg hb hs y T v)
      (SecondVariationBilinear.leftOperator (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
        (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T v) x := by
  classical
  let D := NullAugmentation.driver D₀
  have hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[NullAugmentation.augment F P 0] A :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  let rb := fun i y => sourceError D hbg hsg hb hs hnull x y T (b i) (hbg i) (hb i) (hbd i) v
  let rs := fun i j y => sourceError D hbg hsg hb hs hnull x y T (s i j) (hsg i j) (hs i j) (hsd i j) v
  have hrb (i : Fin N) : rb i =o[𝓝 x] (fun y => y-x) := by
    obtain ⟨A,B,hA,hB,hbound⟩ := SecondVariationSourceRate.sourceError_rate D₀ hbg hsg hb hs hbd hsd x T hT
      (b i) (hbg i) (hb i) (hbd i) (hbd2 i) v
    exact SecondVariationPowerBounds.isLittleO_of_bound x hA hB hbound
  have hrs (i j : Fin N) : rs i j =o[𝓝 x] (fun y => y-x) := by
    obtain ⟨A,B,hA,hB,hbound⟩ := SecondVariationSourceRate.sourceError_rate D₀ hbg hsg hb hs hbd hsd x T hT
      (s i j) (hsg i j) (hs i j) (hsd i j) (hsd2 i j) v
    exact SecondVariationPowerBounds.isLittleO_of_bound x hA hB hbound
  have hd : (fun y => driftSource T (fun i => rb i y)) =o[𝓝 x] (fun y => y-x) := by
    have hh := Asymptotics.IsLittleO.sum (s := (Finset.univ : Finset (Fin N)))
      (A := fun i y => ((stateInclusion i).comp (driftOperator T)) (rb i y))
      (fun i _ => (((stateInclusion i).comp (driftOperator T)).isBigO_comp (rb i) (𝓝 x)).trans_isLittleO (hrb i))
    simpa only [driftSource,ContinuousLinearMap.comp_apply,Finset.sum_fn] using hh
  have hn : (fun y => noiseSource D T (fun i j => rs i j y)) =o[𝓝 x] (fun y => y-x) := by
    have hinner (i : Fin N) := Asymptotics.IsLittleO.sum (s := (Finset.univ : Finset (Fin N)))
      (A := fun j y => itoOperator (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) T (rs i j y))
      (fun j _ => ((itoOperator (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) T).isBigO_comp
        (rs i j) (𝓝 x)).trans_isLittleO (hrs i j))
    have hinner' (i : Fin N) : (fun y => ∑ j : Fin N,itoOperator (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) T (rs i j y)) =o[𝓝 x] (fun y => y-x) := by
      simpa only [Finset.sum_fn] using hinner i
    have hh := Asymptotics.IsLittleO.sum (s := (Finset.univ : Finset (Fin N)))
      (A := fun i y => stateInclusion i (∑ j : Fin N,itoOperator (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) T (rs i j y)))
      (fun i _ => ((stateInclusion i).isBigO_comp _ (𝓝 x)).trans_isLittleO (hinner' i))
    simpa only [noiseSource,Finset.sum_fn] using hh
  let L := sourceLinearMap D (driftRows D hbg hb hs x T) (noiseRows D hsg hb hs x T) T
  have hh := (L.isBigO_comp _ (𝓝 x)).trans_isLittleO (hd.add hn)
  rw [hasFDerivAt_iff_isLittleO]
  exact hh.congr_left (fun y => (SecondVariationResolventError.response_remainder_eq
    D hbg hsg hb hs hbd hsd hnull x y T v).symm)
end SphericalAging.FirstResponseSecondDerivative
