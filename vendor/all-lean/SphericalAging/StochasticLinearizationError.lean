module

public import SphericalAging.StochasticTaylorRemainder

public section

/-! The actual nonlinear solution increment is the genuine Jacobian
resolvent applied to its initial increment plus its proved Taylor source.
This is an exact identity of constructed full-filtration solution classes. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.StochasticLinearizationError
open HardSphereDynamics LocalSDE VariationalCoefficients PredictableLinearCoefficient
open PredictableItoTime PredictableDriftTime VolterraLinearity StochasticTaylorRemainder LinearResolvent
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose]  def driftSource (T : ℝ≥0) (r : Fin N → PredictableProcessL2 F P) : PredictableStateL2 N F P :=
  ∑ i, stateInclusion i (driftOperator T (r i))

@[expose]  def noiseSource (D : BrownianDriver N P F) (T : ℝ≥0)
    (r : Fin N → Fin N → PredictableProcessL2 F P) : PredictableStateL2 N F P :=
  ∑ i, stateInclusion i (∑ j, itoOperator (D.brownian j) (D.coordinateStronglyMeasurable j)
    (D.filtered j) T (r i j))

 theorem driftSource_norm_le (T : ℝ≥0) (r : Fin N → PredictableProcessL2 F P)
    (C : ℝ) (hC : ∀ i,‖r i‖ ≤ C) : ‖driftSource T r‖ ≤ N*T*C := by
  classical
  unfold driftSource
  calc
    _ ≤ ∑ i : Fin N, ‖stateInclusion i (driftOperator T (r i))‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, (T : ℝ)*C := by
      apply Finset.sum_le_sum
      intro i _
      exact (norm_scalarToStatePredictable_le i _).trans ((norm_driftVolterra_le T _).trans
        (mul_le_mul_of_nonneg_left (hC i) T.coe_nonneg))
    _ = _ := by simp [mul_assoc]

 theorem noiseSource_norm_le (D : BrownianDriver N P F) (T : ℝ≥0)
    (r : Fin N → Fin N → PredictableProcessL2 F P) (C : ℝ) (hC : ∀ i j,‖r i j‖ ≤ C) :
    ‖noiseSource D T r‖ ≤ (N : ℝ)^2*Real.sqrt T*C := by
  classical
  unfold noiseSource
  calc
    _ ≤ ∑ i : Fin N, ‖stateInclusion i (∑ j, itoOperator (D.brownian j)
        (D.coordinateStronglyMeasurable j) (D.filtered j) T (r i j))‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, (N : ℝ)*Real.sqrt T*C := by
      apply Finset.sum_le_sum
      intro i _
      apply (norm_scalarToStatePredictable_le i _).trans
      calc
        _ ≤ ∑ j : Fin N, ‖itoOperator (D.brownian j) (D.coordinateStronglyMeasurable j)
          (D.filtered j) T (r i j)‖ := norm_sum_le _ _
        _ ≤ ∑ _j : Fin N, Real.sqrt T*C := by
          apply Finset.sum_le_sum
          intro j _
          exact (norm_itoVolterra_le (D.brownian j) (D.coordinateStronglyMeasurable j)
            (D.filtered j) T _).trans (mul_le_mul_of_nonneg_left (hC i j) (Real.sqrt_nonneg _))
        _ = _ := by simp [mul_assoc]
    _ = _ := by simp [pow_two,mul_assoc]

 theorem finiteDrift_linearization {X : ℝ≥0 → Ω → State N}
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ omega ∂P, Continuous (fun t => X t omega))
    {K : ℝ≥0} {b : Fin N → State N → ℝ}
    (hg : ∀ i, ContDiff ℝ ∞ (b i)) (hb : ∀ i, LipschitzWith K (b i))
    (T : ℝ≥0) (U V : PredictableStateL2 N F P) :
    PredictableDriftTime.finiteDriftPicardMap hb T V-PredictableDriftTime.finiteDriftPicardMap hb T U =
      LinearVariationalSDE.finiteDriftPicardMap (fun i => derivativeRow X hXa hXc (hg i) (hb i) T) T (V-U)+
      driftSource T (fun i => remainder hXa hXc (hg i) (hb i) T U V) := by
  classical
  unfold PredictableDriftTime.finiteDriftPicardMap PredictableDriftTime.driftCoefficientMap
    LinearVariationalSDE.finiteDriftPicardMap LinearVariationalSDE.driftCoefficientMap driftSource
  rw [← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change stateInclusion i (driftOperator T (predictableCoefficient (hb i) V T))-
    stateInclusion i (driftOperator T (predictableCoefficient (hb i) U T)) =
    stateInclusion i (driftOperator T (apply (derivativeRow X hXa hXc (hg i) (hb i) T) (V-U)))+
    stateInclusion i (driftOperator T (remainder hXa hXc (hg i) (hb i) T U V))
  simp only [remainder,map_sub]
  abel

 theorem finiteNoise_linearization {X : ℝ≥0 → Ω → State N}
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ omega ∂P, Continuous (fun t => X t omega))
    (D : BrownianDriver N P F) {K : ℝ≥0} {s : Fin N → Fin N → State N → ℝ}
    (hg : ∀ i j, ContDiff ℝ ∞ (s i j)) (hs : ∀ i j, LipschitzWith K (s i j))
    (T : ℝ≥0) (U V : PredictableStateL2 N F P) :
    PredictableItoTime.finiteNoisePicardMap D hs T V-PredictableItoTime.finiteNoisePicardMap D hs T U =
      LinearVariationalSDE.finiteNoisePicardMap D (fun i j => derivativeRow X hXa hXc (hg i j) (hs i j) T) T (V-U)+
      noiseSource D T (fun i j => remainder hXa hXc (hg i j) (hs i j) T U V) := by
  classical
  unfold PredictableItoTime.finiteNoisePicardMap PredictableItoTime.stochasticCoefficientMap
    LinearVariationalSDE.finiteNoisePicardMap LinearVariationalSDE.stochasticCoefficientMap noiseSource
  rw [← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change stateInclusion i (∑ j, itoOperator (D.brownian j) (D.coordinateStronglyMeasurable j)
      (D.filtered j) T (predictableCoefficient (hs i j) V T))-
    stateInclusion i (∑ j, itoOperator (D.brownian j) (D.coordinateStronglyMeasurable j)
      (D.filtered j) T (predictableCoefficient (hs i j) U T)) =
    stateInclusion i (∑ j, itoOperator (D.brownian j) (D.coordinateStronglyMeasurable j)
      (D.filtered j) T (apply (derivativeRow X hXa hXc (hg i j) (hs i j) T) (V-U)))+
    stateInclusion i (∑ j, itoOperator (D.brownian j) (D.coordinateStronglyMeasurable j)
      (D.filtered j) T (remainder hXa hXc (hg i j) (hs i j) T U V))
  simp only [remainder,map_sub,Finset.sum_sub_distrib]
  abel

 theorem nonlinear_increment_resolvent {X : ℝ≥0 → Ω → State N}
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ omega ∂P, Continuous (fun t => X t omega))
    (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i, ContDiff ℝ ∞ (b i)) (hsg : ∀ i j, ContDiff ℝ ∞ (s i j))
    (hb : ∀ i, LipschitzWith Kb (b i)) (hs : ∀ i j, LipschitzWith Ks (s i j))
    (T : ℝ≥0) (U V : PredictableStateL2 N F P) (x y : State N)
    (hU : U = initialClass (F := F) (P := P) x T+
      PredictableDriftTime.finiteDriftPicardMap hb T U+PredictableItoTime.finiteNoisePicardMap D hs T U)
    (hV : V = initialClass (F := F) (P := P) y T+
      PredictableDriftTime.finiteDriftPicardMap hb T V+PredictableItoTime.finiteNoisePicardMap D hs T V) :
    V-U = sourceLinearMap D
      (fun i => derivativeRow X hXa hXc (hbg i) (hb i) T)
      (fun i j => derivativeRow X hXa hXc (hsg i j) (hs i j) T) T
      (initialClass (y-x) T+driftSource T (fun i => remainder hXa hXc (hbg i) (hb i) T U V)+
        noiseSource D T (fun i j => remainder hXa hXc (hsg i j) (hs i j) T U V)) := by
  apply (LinearVariationalSDE.exists_unique_picard_fixedPoint D _ _ T _).choose_spec.2
  rw [PicardDependence.initialClass_sub]
  have h := congrArg₂ (fun v u : PredictableStateL2 N F P => v-u) hV hU
  have hb' := finiteDrift_linearization hXa hXc hbg hb T U V
  have hs' := finiteNoise_linearization hXa hXc D hsg hs T U V
  calc
    V-U = initialClass y T-initialClass x T+
      (PredictableDriftTime.finiteDriftPicardMap hb T V-PredictableDriftTime.finiteDriftPicardMap hb T U)+
      (PredictableItoTime.finiteNoisePicardMap D hs T V-PredictableItoTime.finiteNoisePicardMap D hs T U) :=
        h.trans (by abel)
    _ = _ := by rw [hb',hs']; abel
end SphericalAging.StochasticLinearizationError
