module

public import SphericalAging.SecondVariationalSDE
public import SphericalAging.HessianInitialSource

public section
/-! The actual second strong variational response is a continuous bilinear
map of its two initial directions. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.SecondVariationBilinear
open HardSphereDynamics LocalSDE StochasticLinearizationError LinearResolvent
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
section Flow
variable (D : BrownianDriver N P F) {Kb Ks Lb Ls : ℝ≥0}
  {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
  (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
  (hbd : ∀ i,LipschitzWith Lb (fderiv ℝ (b i)))
  (hsd : ∀ i j,LipschitzWith Ls (fderiv ℝ (s i j)))
  (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
  (x : State N) (T : ℝ≥0)

theorem responseClass_add_left (v w z : State N) :
    SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull x T (v+z) w=SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull x T v w+SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull x T z w := by
  have hdb (i : Fin N) := HessianInitialSource.source_add_left D hbg hsg hb hs hnull x T (b i) (hbg i) (hbd i) v w z
  have hds (i j : Fin N) := HessianInitialSource.source_add_left D hbg hsg hb hs hnull x T (s i j) (hsg i j) (hsd i j) v w z
  have hdbe (i : Fin N) : SecondVariationalSDE.driftSource D hbg hsg hb hs hbd hnull x T (v+z) w i=
      SecondVariationalSDE.driftSource D hbg hsg hb hs hbd hnull x T v w i+SecondVariationalSDE.driftSource D hbg hsg hb hs hbd hnull x T z w i := hdb i
  have hdse (i j : Fin N) : SecondVariationalSDE.noiseSource D hbg hsg hb hs hsd hnull x T (v+z) w i j=
      SecondVariationalSDE.noiseSource D hbg hsg hb hs hsd hnull x T v w i j+SecondVariationalSDE.noiseSource D hbg hsg hb hs hsd hnull x T z w i j := hds i j
  simp only [SecondVariationalSDE.responseClass,L2AffineVariationalSolution.responseClass,
    ← sourceLinearMap_apply,hdbe,hdse,driftSource,noiseSource,map_add,Finset.sum_add_distrib,smul_add]
  abel

theorem responseClass_smul_left (c : ℝ) (v w : State N) :
    SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull x T (c • v) w=c • SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull x T v w := by
  have hdb (i : Fin N) := HessianInitialSource.source_smul_left D hbg hsg hb hs hnull x T (b i) (hbg i) (hbd i) c v w
  have hds (i j : Fin N) := HessianInitialSource.source_smul_left D hbg hsg hb hs hnull x T (s i j) (hsg i j) (hsd i j) c v w
  have hdbe (i : Fin N) : SecondVariationalSDE.driftSource D hbg hsg hb hs hbd hnull x T (c • v) w i=
      c • SecondVariationalSDE.driftSource D hbg hsg hb hs hbd hnull x T v w i := hdb i
  have hdse (i j : Fin N) : SecondVariationalSDE.noiseSource D hbg hsg hb hs hsd hnull x T (c • v) w i j=
      c • SecondVariationalSDE.noiseSource D hbg hsg hb hs hsd hnull x T v w i j := hds i j
  simp only [SecondVariationalSDE.responseClass,L2AffineVariationalSolution.responseClass,
    ← sourceLinearMap_apply,hdbe,hdse,driftSource,noiseSource,map_smul,← Finset.smul_sum,← smul_add]

theorem responseClass_add_right (v w z : State N) :
    SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull x T v (w+z)=SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull x T v w+SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull x T v z := by
  have hdb (i : Fin N) := HessianInitialSource.source_add_right D hbg hsg hb hs hnull x T (b i) (hbg i) (hbd i) v w z
  have hds (i j : Fin N) := HessianInitialSource.source_add_right D hbg hsg hb hs hnull x T (s i j) (hsg i j) (hsd i j) v w z
  have hdbe (i : Fin N) : SecondVariationalSDE.driftSource D hbg hsg hb hs hbd hnull x T v (w+z) i=
      SecondVariationalSDE.driftSource D hbg hsg hb hs hbd hnull x T v w i+SecondVariationalSDE.driftSource D hbg hsg hb hs hbd hnull x T v z i := hdb i
  have hdse (i j : Fin N) : SecondVariationalSDE.noiseSource D hbg hsg hb hs hsd hnull x T v (w+z) i j=
      SecondVariationalSDE.noiseSource D hbg hsg hb hs hsd hnull x T v w i j+SecondVariationalSDE.noiseSource D hbg hsg hb hs hsd hnull x T v z i j := hds i j
  simp only [SecondVariationalSDE.responseClass,L2AffineVariationalSolution.responseClass,
    ← sourceLinearMap_apply,hdbe,hdse,driftSource,noiseSource,map_add,Finset.sum_add_distrib,smul_add]
  abel

theorem responseClass_smul_right (c : ℝ) (v w : State N) :
    SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull x T v (c • w)=c • SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull x T v w := by
  have hdb (i : Fin N) := HessianInitialSource.source_smul_right D hbg hsg hb hs hnull x T (b i) (hbg i) (hbd i) c v w
  have hds (i j : Fin N) := HessianInitialSource.source_smul_right D hbg hsg hb hs hnull x T (s i j) (hsg i j) (hsd i j) c v w
  have hdbe (i : Fin N) : SecondVariationalSDE.driftSource D hbg hsg hb hs hbd hnull x T v (c • w) i=
      c • SecondVariationalSDE.driftSource D hbg hsg hb hs hbd hnull x T v w i := hdb i
  have hdse (i j : Fin N) : SecondVariationalSDE.noiseSource D hbg hsg hb hs hsd hnull x T v (c • w) i j=
      c • SecondVariationalSDE.noiseSource D hbg hsg hb hs hsd hnull x T v w i j := hds i j
  simp only [SecondVariationalSDE.responseClass,L2AffineVariationalSolution.responseClass,
    ← sourceLinearMap_apply,hdbe,hdse,driftSource,noiseSource,map_smul,← Finset.smul_sum,← smul_add]

@[expose] def leftLinearMap (w : State N) : State N →ₗ[ℝ] PredictableStateL2 N F P where
  toFun := fun v => SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull x T v w
  map_add' v z := responseClass_add_left D hbg hsg hb hs hbd hsd hnull x T v w z
  map_smul' c v := responseClass_smul_left D hbg hsg hb hs hbd hsd hnull x T c v w

@[expose] def leftOperator (w : State N) : State N →L[ℝ] PredictableStateL2 N F P :=
  (leftLinearMap D hbg hsg hb hs hbd hsd hnull x T w).toContinuousLinearMap

@[simp] theorem leftOperator_apply (v w : State N) :
    leftOperator D hbg hsg hb hs hbd hsd hnull x T w v=SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull x T v w := rfl

@[expose] def bilinearLinearMap : State N →ₗ[ℝ] (State N →L[ℝ] PredictableStateL2 N F P) where
  toFun := leftOperator D hbg hsg hb hs hbd hsd hnull x T
  map_add' w z := by
    apply ContinuousLinearMap.ext
    intro v
    exact responseClass_add_right D hbg hsg hb hs hbd hsd hnull x T v w z
  map_smul' c w := by
    apply ContinuousLinearMap.ext
    intro v
    exact responseClass_smul_right D hbg hsg hb hs hbd hsd hnull x T c v w

@[expose] def bilinearOperator : State N →L[ℝ] State N →L[ℝ] PredictableStateL2 N F P :=
  LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := State N)
    (F' := State N →L[ℝ] PredictableStateL2 N F P) (bilinearLinearMap D hbg hsg hb hs hbd hsd hnull x T)

@[simp] theorem bilinearOperator_apply (v w : State N) :
    bilinearOperator D hbg hsg hb hs hbd hsd hnull x T w v=SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull x T v w := rfl

end Flow
end SphericalAging.SecondVariationBilinear
