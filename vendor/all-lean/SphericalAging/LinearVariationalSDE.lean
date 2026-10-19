module

public import SphericalAging.PredictableLinearCoefficient
public import SphericalAging.GlobalSDE
public import SphericalAging.PicardDependence

public section

/-! Genuine linear matrix-driven stochastic variational equations with
bounded random predictable coefficients. Exponential weighting proves
existence on every finite horizon, using actual full-filtration Itô maps. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.LinearVariationalSDE
open HardSphereDynamics PredictableItoTime PredictableDriftTime WeightedPredictable
open PredictableLinearCoefficient LocalSDE
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def driftCoefficientMap {Kb : ℝ≥0} (a : Coefficient (N := N) (F := F) (P := P) Kb)
    (T : ℝ≥0) (U : PredictableStateL2 N F P) : PredictableProcessL2 F P :=
  driftVolterra T (apply a U)

@[expose] def stochasticCoefficientMap (D : BrownianDriver N P F) (j : Fin N) {Ks : ℝ≥0}
    (a : Coefficient (N := N) (F := F) (P := P) Ks)
    (T : ℝ≥0) (U : PredictableStateL2 N F P) : PredictableProcessL2 F P :=
  itoVolterra (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) T (apply a U)

@[expose] def finiteDriftPicardMap {Kb : ℝ≥0} (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (T : ℝ≥0) (U : PredictableStateL2 N F P) : PredictableStateL2 N F P :=
  ∑ i, scalarToStatePredictable i (driftCoefficientMap (a i) T U)

@[expose] def finiteNoisePicardMap (D : BrownianDriver N P F) {Ks : ℝ≥0}
    (a : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (T : ℝ≥0) (U : PredictableStateL2 N F P) : PredictableStateL2 N F P :=
  ∑ i, scalarToStatePredictable i (∑ j, stochasticCoefficientMap D j (a i j) T U)

theorem norm_weighted_driftCoefficient_sub_le {Kb : ℝ≥0}
    (hb : Coefficient (N := N) (F := F) (P := P) Kb) (α : ℝ) (T : ℝ≥0) (Cd : ℝ≥0)
    (hd : ∀ A : PredictableProcessL2 F P,
      ‖multiply α T (driftVolterra T A)‖ ≤ Cd * ‖multiply α T A‖)
    (U V : PredictableStateL2 N F P) :
    ‖multiply α T (driftCoefficientMap hb T U - driftCoefficientMap hb T V)‖ ≤
      (Cd : ℝ) * Kb * ‖multiply α T (U-V)‖ := by
  unfold driftCoefficientMap
  rw [← driftVolterra_sub]
  calc
    _ ≤ (Cd : ℝ) * ‖multiply α T (apply hb U - apply hb V)‖ := hd _
    _ ≤ (Cd : ℝ) * ((Kb : ℝ) * ‖multiply α T (U-V)‖) :=
      mul_le_mul_of_nonneg_left (norm_weighted_sub_le hb α T U V) Cd.coe_nonneg
    _ = _ := by ring

theorem norm_weighted_stochasticCoefficient_sub_le (D : BrownianDriver N P F) (j : Fin N)
    {Ks : ℝ≥0} (hs : Coefficient (N := N) (F := F) (P := P) Ks)
    (α : ℝ) (T : ℝ≥0) (Ci : ℝ≥0)
    (hi : ∀ A : PredictableProcessL2 F P,
      ‖multiply α T (itoVolterra (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) T A)‖ ≤
        Ci * ‖multiply α T A‖) (U V : PredictableStateL2 N F P) :
    ‖multiply α T (stochasticCoefficientMap D j hs T U - stochasticCoefficientMap D j hs T V)‖ ≤
      (Ci : ℝ) * Ks * ‖multiply α T (U-V)‖ := by
  unfold stochasticCoefficientMap
  rw [← itoVolterra_sub]
  calc
    _ ≤ (Ci : ℝ) * ‖multiply α T (apply hs U - apply hs V)‖ := hi _
    _ ≤ (Ci : ℝ) * ((Ks : ℝ) * ‖multiply α T (U-V)‖) :=
      mul_le_mul_of_nonneg_left (norm_weighted_sub_le hs α T U V) Ci.coe_nonneg
    _ = _ := by ring

theorem norm_weighted_finiteDrift_sub_le {Kb : ℝ≥0}
    (hb : Fin N → Coefficient (N := N) (F := F) (P := P) Kb) (α : ℝ) (T : ℝ≥0) (Cd : ℝ≥0)
    (hd : ∀ A : PredictableProcessL2 F P,
      ‖multiply α T (driftVolterra T A)‖ ≤ Cd * ‖multiply α T A‖)
    (U V : PredictableStateL2 N F P) :
    ‖multiply α T (finiteDriftPicardMap hb T U - finiteDriftPicardMap hb T V)‖ ≤
      (N : ℝ) * Cd * Kb * ‖multiply α T (U-V)‖ := by
  unfold finiteDriftPicardMap
  rw [← Finset.sum_sub_distrib, multiply_sum]
  calc
    _ ≤ ∑ i : Fin N, ‖multiply α T (scalarToStatePredictable i (driftCoefficientMap (hb i) T U) -
        scalarToStatePredictable i (driftCoefficientMap (hb i) T V))‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, (Cd : ℝ) * Kb * ‖multiply α T (U-V)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [← scalarToStatePredictable_sub, multiply_scalarToState]
      exact (norm_scalarToStatePredictable_le i _).trans
        (norm_weighted_driftCoefficient_sub_le (hb i) α T Cd hd U V)
    _ = _ := by simp; ring

theorem norm_weighted_finiteNoise_sub_le (D : BrownianDriver N P F)
    {Ks : ℝ≥0}
    (hs : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks) (α : ℝ) (T : ℝ≥0) (Ci : ℝ≥0)
    (hi : ∀ j (A : PredictableProcessL2 F P),
      ‖multiply α T (itoVolterra (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) T A)‖ ≤
        Ci * ‖multiply α T A‖) (U V : PredictableStateL2 N F P) :
    ‖multiply α T (finiteNoisePicardMap D hs T U - finiteNoisePicardMap D hs T V)‖ ≤
      (N : ℝ)^2 * Ci * Ks * ‖multiply α T (U-V)‖ := by
  unfold finiteNoisePicardMap
  rw [← Finset.sum_sub_distrib, multiply_sum]
  calc
    _ ≤ ∑ i : Fin N, ‖multiply α T (scalarToStatePredictable i
        (∑ j : Fin N, stochasticCoefficientMap D j (hs i j) T U) - scalarToStatePredictable i
          (∑ j : Fin N, stochasticCoefficientMap D j (hs i j) T V))‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, (N : ℝ) * ((Ci : ℝ) * Ks * ‖multiply α T (U-V)‖) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← scalarToStatePredictable_sub, multiply_scalarToState]
      calc
        _ ≤ ‖multiply α T ((∑ j : Fin N, stochasticCoefficientMap D j (hs i j) T U) -
            (∑ j : Fin N, stochasticCoefficientMap D j (hs i j) T V))‖ := norm_scalarToStatePredictable_le i _
        _ ≤ ∑ j : Fin N, ‖multiply α T (stochasticCoefficientMap D j (hs i j) T U -
            stochasticCoefficientMap D j (hs i j) T V)‖ := by
          rw [← Finset.sum_sub_distrib, multiply_sum]
          exact norm_sum_le _ _
        _ ≤ ∑ _j : Fin N, (Ci : ℝ) * Ks * ‖multiply α T (U-V)‖ :=
          Finset.sum_le_sum (fun j _ => norm_weighted_stochasticCoefficient_sub_le D j (hs i j)
            α T Ci (hi j) U V)
        _ = _ := by simp
    _ = _ := by simp; ring

@[expose] def picardMap (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    (hb : Fin N → Coefficient (N := N) (F := F) (P := P) Kb) (hs : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (α : ℝ) (T : ℝ≥0) (A U : PredictableStateL2 N F P) : PredictableStateL2 N F P :=
  multiply α T (A + finiteDriftPicardMap hb T (multiply (-α) T U) +
    finiteNoisePicardMap D hs T (multiply (-α) T U))

/-- Genuine Banach construction for the transformed full SDE Picard map.
The scalar operator norm lemmas are subsequently instantiated by the proved
weighted kernel estimates. -/
theorem exists_unique_picard_fixedPoint_of_operator_bounds (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    (hb : Fin N → Coefficient (N := N) (F := F) (P := P) Kb) (hs : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (α : ℝ) (T : ℝ≥0) (Cd Ci : ℝ≥0) (A : PredictableStateL2 N F P)
    (hd : ∀ V : PredictableProcessL2 F P,
      ‖multiply α T (driftVolterra T V)‖ ≤ Cd * ‖multiply α T V‖)
    (hi : ∀ j (V : PredictableProcessL2 F P),
      ‖multiply α T (itoVolterra (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) T V)‖ ≤
        Ci * ‖multiply α T V‖)
    (hsmall : (N : ℝ≥0) * Cd * Kb + (N : ℝ≥0)^2 * Ci * Ks < 1) :
    ∃ U : PredictableStateL2 N F P, U = A + finiteDriftPicardMap hb T U + finiteNoisePicardMap D hs T U ∧
      ∀ V, V = A + finiteDriftPicardMap hb T V + finiteNoisePicardMap D hs T V → V = U := by
  have : Fact (F.predictable ≤ (inferInstance : MeasurableSpace (ℝ≥0 × Ω))) := ⟨predictable_le_prod F⟩
  let f := picardMap D hb hs α T A
  have hl : LipschitzWith ((N : ℝ≥0) * Cd * Kb + (N : ℝ≥0)^2 * Ci * Ks) f := by
    apply LipschitzWith.of_dist_le_mul
    intro U V
    simp only [dist_eq_norm]
    have he : f U - f V =
        multiply α T (finiteDriftPicardMap hb T (multiply (-α) T U) -
          finiteDriftPicardMap hb T (multiply (-α) T V)) +
        multiply α T (finiteNoisePicardMap D hs T (multiply (-α) T U) -
          finiteNoisePicardMap D hs T (multiply (-α) T V)) := by
      dsimp only [f, picardMap]
      rw [← multiply_sub]
      have hgroup : A + finiteDriftPicardMap hb T (multiply (-α) T U) +
          finiteNoisePicardMap D hs T (multiply (-α) T U) -
          (A + finiteDriftPicardMap hb T (multiply (-α) T V) +
            finiteNoisePicardMap D hs T (multiply (-α) T V)) =
          (finiteDriftPicardMap hb T (multiply (-α) T U) - finiteDriftPicardMap hb T (multiply (-α) T V)) +
          (finiteNoisePicardMap D hs T (multiply (-α) T U) - finiteNoisePicardMap D hs T (multiply (-α) T V)) := by abel
      rw [hgroup, multiply_add]
    have hweight : multiply α T (multiply (-α) T U - multiply (-α) T V) = U-V := by
      rw [multiply_sub, multiply_inverse, multiply_inverse]
    rw [he]
    calc
      _ ≤ ‖multiply α T (finiteDriftPicardMap hb T (multiply (-α) T U) -
          finiteDriftPicardMap hb T (multiply (-α) T V))‖ +
        ‖multiply α T (finiteNoisePicardMap D hs T (multiply (-α) T U) -
          finiteNoisePicardMap D hs T (multiply (-α) T V))‖ := norm_add_le _ _
      _ ≤ (N : ℝ) * Cd * Kb * ‖multiply α T (multiply (-α) T U - multiply (-α) T V)‖ +
          (N : ℝ)^2 * Ci * Ks * ‖multiply α T (multiply (-α) T U - multiply (-α) T V)‖ :=
        add_le_add (norm_weighted_finiteDrift_sub_le hb α T Cd hd _ _)
          (norm_weighted_finiteNoise_sub_le D hs α T Ci hi _ _)
      _ = _ := by rw [hweight]; simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast]; ring
  have hc : ContractingWith ((N : ℝ≥0) * Cd * Kb + (N : ℝ≥0)^2 * Ci * Ks) f := ⟨hsmall, hl⟩
  let W := hc.fixedPoint
  let U := multiply (-α) T W
  have hfix : f W = W := hc.fixedPoint_isFixedPt.eq
  have hU : U = A + finiteDriftPicardMap hb T U + finiteNoisePicardMap D hs T U := by
    have hh := congrArg (multiply (-α) T) hfix
    simpa only [f, picardMap, inverse_multiply, U] using hh.symm
  refine ⟨U, hU, ?_⟩
  intro V hV
  have hVfix : f (multiply α T V) = multiply α T V := by
    dsimp only [f, picardMap]
    rw [inverse_multiply, ← hV]
  have hVW : multiply α T V = W := hc.fixedPoint_unique hVfix
  have h := congrArg (multiply (-α) T) hVW
  simpa only [inverse_multiply, U] using h

theorem exists_unique_picard_fixedPoint (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    (hb : Fin N → Coefficient (N := N) (F := F) (P := P) Kb) (hsigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (T : ℝ≥0) (A : PredictableStateL2 N F P) :
    ∃ U : PredictableStateL2 N F P, U = A + finiteDriftPicardMap hb T U + finiteNoisePicardMap D hsigma T U ∧
      ∀ V, V = A + finiteDriftPicardMap hb T V + finiteNoisePicardMap D hsigma T V → V = U := by
  obtain ⟨α,hα,Cd,Ci,hCd,hCi,hsmall⟩ := WeightedPicard.exists_contraction_parameters N Kb Ks T
  apply exists_unique_picard_fixedPoint_of_operator_bounds D hb hsigma α T Cd Ci A
  · intro V
    rw [hCd]
    exact WeightedDriftNorm.norm_weighted_driftVolterra_le hα T V
  · intro j V
    rw [hCi, one_div]
    exact WeightedItoNorm.norm_weighted_itoVolterra_le (D.brownian j)
      (D.coordinateStronglyMeasurable j) (D.filtered j) hα T V
  · exact hsmall

@[expose] def coordinateVersion (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    (hb : Fin N → Coefficient (N := N) (F := F) (P := P) Kb) (hsigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (x0 : State N) (T : ℝ≥0) (U : PredictableStateL2 N F P)
    (i : Fin N) (t : ℝ≥0) (omega : Ω) : ℝ :=
  x0 i + driftVersion (apply (hb i) U) T t omega +
    ∑ j : Fin N, itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j)
      (apply (hsigma i j) U) t omega

@[expose] def version (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    (hb : Fin N → Coefficient (N := N) (F := F) (P := P) Kb) (hsigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (x0 : State N) (T : ℝ≥0) (U : PredictableStateL2 N F P)
    (t : ℝ≥0) (omega : Ω) : State N :=
  ∑ i : Fin N, coordinateVersion D hb hsigma x0 T U i t omega • basisVector i

theorem coordinateVersion_stronglyAdapted (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    (hb : Fin N → Coefficient (N := N) (F := F) (P := P) Kb) (hsigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (x0 : State N) (T : ℝ≥0) (U : PredictableStateL2 N F P) (i : Fin N) :
    StronglyAdapted F (coordinateVersion D hb hsigma x0 T U i) := by
  intro t
  apply StronglyMeasurable.add
  · exact stronglyMeasurable_const.add (driftVersion_stronglyAdapted _ T t)
  · exact Finset.stronglyMeasurable_fun_sum Finset.univ (fun j _ =>
      itoVersion_stronglyAdapted (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) _ t)

theorem version_stronglyAdapted (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    (hb : Fin N → Coefficient (N := N) (F := F) (P := P) Kb) (hsigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (x0 : State N) (T : ℝ≥0) (U : PredictableStateL2 N F P) :
    StronglyAdapted F (version D hb hsigma x0 T U) := by
  intro t
  exact Finset.stronglyMeasurable_fun_sum Finset.univ (fun i _ =>
    (coordinateVersion_stronglyAdapted D hb hsigma x0 T U i t).smul_const (basisVector i))

theorem coordinateVersion_ae_continuous (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    (hb : Fin N → Coefficient (N := N) (F := F) (P := P) Kb) (hsigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (x0 : State N) (T : ℝ≥0) (U : PredictableStateL2 N F P) (i : Fin N) :
    ∀ᵐ omega ∂P, Continuous (fun t => coordinateVersion D hb hsigma x0 T U i t omega) := by
  have hall : ∀ᵐ omega ∂P, ∀ j : Fin N, Continuous (fun t =>
      itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j)
        (apply (hsigma i j) U) t omega) :=
    ae_all_iff.mpr (fun j => (itoVersion_continuousModification (D.brownian j)
      (D.coordinateStronglyMeasurable j) (D.filtered j) _).continuous_paths)
  filter_upwards [driftVersion_ae_continuous (apply (hb i) U) T, hall]
    with omega hbcont hscont
  exact (continuous_const.add hbcont).add (continuous_finsetSum Finset.univ (fun j _ => hscont j))

theorem version_ae_continuous (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    (hb : Fin N → Coefficient (N := N) (F := F) (P := P) Kb) (hsigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (x0 : State N) (T : ℝ≥0) (U : PredictableStateL2 N F P) :
    ∀ᵐ omega ∂P, Continuous (fun t => version D hb hsigma x0 T U t omega) := by
  have hall := ae_all_iff.mpr (fun i => coordinateVersion_ae_continuous D hb hsigma x0 T U i)
  filter_upwards [hall] with omega homega
  exact continuous_finsetSum Finset.univ (fun i _ => (homega i).smul continuous_const)


theorem finiteDriftPicardMap_coeFn {Kb : ℝ≥0}
    (hb : Fin N → Coefficient (N := N) (F := F) (P := P) Kb) (T : ℝ≥0) (U : PredictableStateL2 N F P) :
    (finiteDriftPicardMap hb T U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (fun p => if p.1 ∈ Ioc (0 : ℝ≥0) T then
        ∑ i : Fin N, driftVersion (apply (hb i) U) T p.1 p.2 • basisVector i
      else 0) := by
  have hsum := sumState_coeFn (fun i => scalarToStatePredictable i (driftCoefficientMap (hb i) T U))
  have hincl := ae_all_iff.mpr (fun i : Fin N => scalarToStatePredictable_coeFn i
    (driftCoefficientMap (hb i) T U))
  have hcoeff : ∀ᵐ p ∂nonnegativeLebesgueMeasure.prod P, ∀ i : Fin N,
      (driftCoefficientMap (hb i) T U : TimeProcessL2 P) p =
        FourPapersCommon.continuousAdaptedTimeCut
          (driftVersion (apply (hb i) U) T) T p :=
    ae_all_iff.mpr (fun i => (driftVersion_timeCut_memLp (apply (hb i) U) T).coeFn_toLp)
  filter_upwards [hsum, hincl, hcoeff] with p hp hi hc
  unfold finiteDriftPicardMap
  rw [hp]
  by_cases ht : p.1 ∈ Ioc (0 : ℝ≥0) T
  · simp [hi, hc, FourPapersCommon.continuousAdaptedTimeCut, ht]
  · simp [hi, hc, FourPapersCommon.continuousAdaptedTimeCut, ht]

theorem finiteNoisePicardMap_coeFn (D : BrownianDriver N P F) {Ks : ℝ≥0}
    
    (hsigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks) (T : ℝ≥0) (U : PredictableStateL2 N F P) :
    (finiteNoisePicardMap D hsigma T U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (fun p => if p.1 ∈ Ioc (0 : ℝ≥0) T then
        ∑ i : Fin N, (∑ j : Fin N, itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j)
          (D.filtered j) (apply (hsigma i j) U) p.1 p.2) • basisVector i
      else 0) := by
  have hsum := sumState_coeFn (fun i => scalarToStatePredictable i
    (∑ j : Fin N, stochasticCoefficientMap D j (hsigma i j) T U))
  have hincl := ae_all_iff.mpr (fun i : Fin N => scalarToStatePredictable_coeFn i
    (∑ j : Fin N, stochasticCoefficientMap D j (hsigma i j) T U))
  have hinner := ae_all_iff.mpr (fun i : Fin N => sumScalar_coeFn
    (fun j => stochasticCoefficientMap D j (hsigma i j) T U))
  have hcoeff : ∀ᵐ p ∂nonnegativeLebesgueMeasure.prod P, ∀ i j : Fin N,
      (stochasticCoefficientMap D j (hsigma i j) T U : TimeProcessL2 P) p =
        FourPapersCommon.continuousAdaptedTimeCut
          (itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j)
            (D.filtered j) (apply (hsigma i j) U)) T p :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j =>
      (itoVersion_timeCut_memLp (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j)
        (apply (hsigma i j) U) T).coeFn_toLp))
  filter_upwards [hsum, hincl, hinner, hcoeff] with p hp hi hj hc
  unfold finiteNoisePicardMap
  rw [hp]
  by_cases ht : p.1 ∈ Ioc (0 : ℝ≥0) T
  · simp only [ite_eq_left ht]
    apply Finset.sum_congr rfl
    intro i _
    rw [hi i, hj i]
    simp only [hc, FourPapersCommon.continuousAdaptedTimeCut, ite_eq_left ht]
  · simp only [ite_eq_right ht]
    have hz : ∀ i : Fin N, (scalarToStatePredictable i
        (∑ j : Fin N, stochasticCoefficientMap D j (hsigma i j) T U) :
          Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) p = 0 := by
      intro i
      rw [hi i, hj i]
      simp only [hc, FourPapersCommon.continuousAdaptedTimeCut, ite_eq_right ht,
        Finset.sum_const_zero, zero_smul]
    simp only [hz, Finset.sum_const_zero]

theorem version_timeCut_eq_fixedPoint_ae (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    (hb : Fin N → Coefficient (N := N) (F := F) (P := P) Kb) (hsigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (x0 : State N) (T : ℝ≥0) (U : PredictableStateL2 N F P)
    (hfixed : U = initialClass (F := F) (P := P) x0 T + finiteDriftPicardMap hb T U + finiteNoisePicardMap D hsigma T U) :
    ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun p => version D hb hsigma x0 T U p.1 p.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) := by
  have hadd := Lp.coeFn_add
    ((initialClass (F := F) (P := P) x0 T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) +
      (finiteDriftPicardMap hb T U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
    (finiteNoisePicardMap D hsigma T U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
  have hadd' := Lp.coeFn_add
    (initialClass (F := F) (P := P) x0 T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
    (finiteDriftPicardMap hb T U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
  filter_upwards [hadd, hadd', initialClass_coeFn (F := F) (P := P) x0 T, finiteDriftPicardMap_coeFn hb T U,
    finiteNoisePicardMap_coeFn D hsigma T U] with p hp hp' h0 hbcoe hscoe
  conv_rhs => rw [hfixed]
  change _ = (((initialClass (F := F) (P := P) x0 T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) +
    (finiteDriftPicardMap hb T U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))) +
    (finiteNoisePicardMap D hsigma T U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))) p
  rw [hp, Pi.add_apply, hp', Pi.add_apply, h0, hbcoe, hscoe]
  by_cases ht : p.1 ∈ Ioc (0 : ℝ≥0) T
  · simp only [show p ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨ht, mem_univ _⟩,
      indicator_of_mem, ht, ite_eq_left]
    simp only [version, coordinateVersion, add_smul, Finset.sum_add_distrib, state_sum_basis]
  · simp [ht]


theorem version_apply (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    (hb : Fin N → Coefficient (N := N) (F := F) (P := P) Kb) (hsigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (x0 : State N) (T : ℝ≥0) (U : PredictableStateL2 N F P) (t : ℝ≥0) (omega : Ω) (i : Fin N) :
    (version D hb hsigma x0 T U t omega) i = coordinateVersion D hb hsigma x0 T U i t omega := by
  simp [version, basisVector, Pi.single_apply]


section ActualLinearSolution
variable {X : ℝ≥0 → Ω → State N} {U : PredictableStateL2 N F P} {T : ℝ≥0}
  (hXeq : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun q => X q.1 q.2))
    =ᵐ[nonnegativeLebesgueMeasure.prod P] (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
include hXeq

omit [IsProbabilityMeasure P] in
theorem apply_eq_actual {K : ℝ≥0} (a : Coefficient (N := N) (F := F) (P := P) K) :
    (apply a U : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun s omega => a.value (s,omega) (X s omega)) T := by
  filter_upwards [hXeq,apply_coeFn a U] with q hq ha
  rw [ha]
  by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
  · have hx : X q.1 q.2 = (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q := by
      simpa only [indicator_of_mem (show q ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨ht,mem_univ _⟩)] using hq
    simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,hx]
  · have hu : (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q = 0 := by
      simpa only [indicator_of_notMem (show q ∉ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from fun h => ht h.1)] using hq.symm
    simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false,hu,map_zero]

theorem driftVersion_eq_actual {K : ℝ≥0} (a : Coefficient (N := N) (F := F) (P := P) K) :
    ∀ᵐ omega ∂P, ∀ t : ℝ≥0, t ≤ T → driftVersion (apply a U) T t omega =
      ∫ s in (0 : ℝ)..(t : ℝ), a.value (s.toNNReal,omega) (X s.toNNReal omega) := by
  have hc : cutRepresentative (apply a U) T =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun s omega => a.value (s,omega) (X s omega)) T := by
    filter_upwards [representative_ae (apply a U),apply_eq_actual hXeq a] with q hr ha
    unfold cutRepresentative FourPapersCommon.FilteredBrownian.predictableTimeFrame
    by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
    · simp only [indicator_of_mem (show q ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨ht,mem_univ _⟩),hr,ha]
    · simp [ht,FourPapersCommon.continuousAdaptedTimeCut]
  have hswap := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hc
  filter_upwards [Measure.ae_ae_of_ae_prod hswap] with omega homega
  intro t ht
  rw [← primitive_eq_real_intervalIntegral (fun q => a.value q (X q.1 q.2)) t omega]
  unfold driftVersion primitive
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae homega,ae_restrict_mem measurableSet_Ioc] with r hr hrt
  change cutRepresentative (apply a U) T (r,omega) =
    FourPapersCommon.continuousAdaptedTimeCut (fun s omega => a.value (s,omega) (X s omega)) T (r,omega) at hr
  rw [hr]
  exact ite_eq_left (show r ∈ Ioc (0 : ℝ≥0) T from ⟨hrt.1,hrt.2.trans ht⟩)
end ActualLinearSolution

/-- Actual linear SDE semantics with coefficient classes identified with
the evaluated coefficients. No fixed-point property is solution data. -/
@[expose] def IsStrongSolutionOn {Kb Ks : ℝ≥0}
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (D : BrownianDriver N P F) (v0 : State N) (X : ℝ≥0 → Ω → State N) (T : ℝ≥0) : Prop :=
  StronglyAdapted F X ∧ (∀ᵐ omega ∂P, Continuous (fun t => X t omega)) ∧
  ∃ A : Fin N → PredictableProcessL2 F P, ∃ U : Fin N → Fin N → PredictableProcessL2 F P,
    (∀ i, (A i : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun s omega => (a i).value (s,omega) (X s omega)) T) ∧
    (∀ i j, (U i j : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun s omega => (sigma i j).value (s,omega) (X s omega)) T) ∧
    ∀ t, t ≤ T → ∀ i, ∀ᵐ omega ∂P, X t omega i = v0 i +
      (∫ s in (0 : ℝ)..(t : ℝ), (a i).value (s.toNNReal,omega) (X s.toNNReal omega)) +
      (driverItoMap D (fun j => FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t (U i j)) : Ω → ℝ) omega

theorem strongSolution_of_fixedPoint (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (v0 : State N) (T : ℝ≥0) (U : PredictableStateL2 N F P)
    (hU : U = initialClass (F := F) (P := P) v0 T + finiteDriftPicardMap a T U + finiteNoisePicardMap D sigma T U) :
    IsStrongSolutionOn a sigma D v0 (version D a sigma v0 T U) T := by
  have hXeq := version_timeCut_eq_fixedPoint_ae D a sigma v0 T U hU
  refine ⟨version_stronglyAdapted D a sigma v0 T U,version_ae_continuous D a sigma v0 T U,
    (fun i => apply (a i) U),(fun i j => apply (sigma i j) U),
    (fun i => apply_eq_actual hXeq (a i)),(fun i j => apply_eq_actual hXeq (sigma i j)),?_⟩
  intro t ht i
  have hi : ∀ᵐ omega ∂P, ∀ j : Fin N,
      (FourPapersCommon.FilteredBrownian.naturalItoIntegral (D.brownian j).toIsPreBrownianReal
        (D.coordinateStronglyMeasurable j) (D.filtered j)
        (FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t (apply (sigma i j) U)) : Ω → ℝ) omega =
      itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) (apply (sigma i j) U) t omega :=
    ae_all_iff.mpr (fun j => (itoVersion_ae_eq (D.brownian j)
      (D.coordinateStronglyMeasurable j) (D.filtered j) (apply (sigma i j) U) t))
  have hn := Lp.coeFn_fun_finsetSum Finset.univ (fun j : Fin N =>
    FourPapersCommon.FilteredBrownian.naturalItoIntegral (D.brownian j).toIsPreBrownianReal
      (D.coordinateStronglyMeasurable j) (D.filtered j)
      (FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t (apply (sigma i j) U)))
  filter_upwards [driftVersion_eq_actual hXeq (a i),hi,hn] with omega hd hi hn
  rw [version_apply,driverItoMap_apply]
  simp only [coordinateVersion,hd t ht,hn,hi]

/-- Actual bounded-predictable matrix variational SDE existence on any
specified finite horizon. -/
theorem exists_strongSolution_on (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (v0 : State N) (T : ℝ≥0) : ∃ X, IsStrongSolutionOn a sigma D v0 X T := by
  obtain ⟨U,hU,_⟩ := exists_unique_picard_fixedPoint D a sigma T (initialClass (F := F) (P := P) v0 T)
  exact ⟨version D a sigma v0 T U,strongSolution_of_fixedPoint D a sigma v0 T U hU⟩

@[expose] def sourceClass (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    (hb : Fin N → Coefficient (N := N) (F := F) (P := P) Kb) (hs : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (T : ℝ≥0) (A : PredictableStateL2 N F P) : PredictableStateL2 N F P :=
  (exists_unique_picard_fixedPoint D hb hs T A).choose

lemma sourceClass_fixedPoint (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    (hb : Fin N → Coefficient (N := N) (F := F) (P := P) Kb) (hs : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (T : ℝ≥0) (A : PredictableStateL2 N F P) :
    sourceClass D hb hs T A = A + finiteDriftPicardMap hb T (sourceClass D hb hs T A) +
      finiteNoisePicardMap D hs T (sourceClass D hb hs T A) :=
  (exists_unique_picard_fixedPoint D hb hs T A).choose_spec.1

lemma weighted_sourceClass_sub_bound (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    (hb : Fin N → Coefficient (N := N) (F := F) (P := P) Kb) (hs : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (α : ℝ) (T : ℝ≥0) (Cd Ci : ℝ≥0)
    (hd : ∀ V : PredictableProcessL2 F P,
      ‖multiply α T (driftVolterra T V)‖ ≤ Cd * ‖multiply α T V‖)
    (hi : ∀ j (V : PredictableProcessL2 F P),
      ‖multiply α T (itoVolterra (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) T V)‖ ≤
        Ci * ‖multiply α T V‖)
    (hsmall : (N : ℝ≥0) * Cd * Kb + (N : ℝ≥0)^2 * Ci * Ks < 1)
    (A B : PredictableStateL2 N F P) :
    ‖multiply α T (sourceClass D hb hs T A - sourceClass D hb hs T B)‖ ≤
      ‖multiply α T (A-B)‖ / (1 - ((N : ℝ) * Cd * Kb + (N : ℝ)^2 * Ci * Ks)) := by
  let U := sourceClass D hb hs T A
  let V := sourceClass D hb hs T B
  have hU := sourceClass_fixedPoint D hb hs T A
  have hV := sourceClass_fixedPoint D hb hs T B
  have heq : U-V = (A-B) + (finiteDriftPicardMap hb T U - finiteDriftPicardMap hb T V) +
      (finiteNoisePicardMap D hs T U - finiteNoisePicardMap D hs T V) := by
    calc
      U-V = (A + finiteDriftPicardMap hb T U + finiteNoisePicardMap D hs T U) -
        (B + finiteDriftPicardMap hb T V + finiteNoisePicardMap D hs T V) := congrArg₂ (·-·) hU hV
      _ = _ := by abel
  have hnorm : ‖multiply α T (U-V)‖ ≤ ‖multiply α T (A-B)‖ +
      ((N : ℝ) * Cd * Kb + (N : ℝ)^2 * Ci * Ks) * ‖multiply α T (U-V)‖ := by
    calc
      _ = ‖multiply α T (A-B) +
        multiply α T (finiteDriftPicardMap hb T U - finiteDriftPicardMap hb T V) +
        multiply α T (finiteNoisePicardMap D hs T U - finiteNoisePicardMap D hs T V)‖ := by
          rw [heq, multiply_add, multiply_add]
      _ ≤ (‖multiply α T (A-B)‖ +
        ‖multiply α T (finiteDriftPicardMap hb T U - finiteDriftPicardMap hb T V)‖) +
        ‖multiply α T (finiteNoisePicardMap D hs T U - finiteNoisePicardMap D hs T V)‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (‖multiply α T (A-B)‖ + (N : ℝ)*Cd*Kb*‖multiply α T (U-V)‖) +
        (N : ℝ)^2*Ci*Ks*‖multiply α T (U-V)‖ :=
          add_le_add (add_le_add le_rfl (norm_weighted_finiteDrift_sub_le hb α T Cd hd U V))
            (norm_weighted_finiteNoise_sub_le D hs α T Ci hi U V)
      _ = _ := by ring
  have hq : ((N : ℝ)*Cd*Kb + (N : ℝ)^2*Ci*Ks) < 1 := by exact_mod_cast hsmall
  apply (le_div_iff₀ (sub_pos.mpr hq)).mpr
  change ‖multiply α T (U-V)‖ * _ ≤ _
  nlinarith

/-- Genuine continuous dependence of the actual Picard class on arbitrary
predictable L² source data, for every finite horizon. The contraction
constants are obtained from the proved actual drift and Itô bounds. -/
theorem sourceClass_lipschitz (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    (hb : Fin N → Coefficient (N := N) (F := F) (P := P) Kb) (hs : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (T : ℝ≥0) : ∃ K : ℝ≥0, LipschitzWith K (sourceClass D hb hs T) := by
  obtain ⟨α, hα, Cd, Ci, hCd, hCi, hsmall⟩ := WeightedPicard.exists_contraction_parameters N Kb Ks T
  have hd : ∀ V : PredictableProcessL2 F P, ‖multiply α T (driftVolterra T V)‖ ≤ Cd * ‖multiply α T V‖ := by
    intro V
    rw [hCd]
    exact WeightedDriftNorm.norm_weighted_driftVolterra_le hα T V
  have hi : ∀ j (V : PredictableProcessL2 F P),
      ‖multiply α T (itoVolterra (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) T V)‖ ≤
        Ci * ‖multiply α T V‖ := by
    intro j V
    rw [hCi, one_div]
    exact WeightedItoNorm.norm_weighted_itoVolterra_le (D.brownian j)
      (D.coordinateStronglyMeasurable j) (D.filtered j) hα T V
  let q : ℝ := (N : ℝ)*Cd*Kb + (N : ℝ)^2*Ci*Ks
  have hq : q < 1 := by dsimp only [q]; exact_mod_cast hsmall
  let C : ℝ := Real.exp (|α| * T) * Real.exp (|α| * T) / (1-q)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨⟨C, hC⟩, LipschitzWith.of_dist_le_mul (fun A B => ?_)⟩
  simp only [dist_eq_norm]
  have hw := weighted_sourceClass_sub_bound D hb hs α T Cd Ci hd hi hsmall A B
  have hu : sourceClass D hb hs T A - sourceClass D hb hs T B =
      multiply (-α) T (multiply α T (sourceClass D hb hs T A - sourceClass D hb hs T B)) :=
    (inverse_multiply α T _).symm
  calc
    _ = ‖multiply (-α) T (multiply α T (sourceClass D hb hs T A - sourceClass D hb hs T B))‖ := congrArg norm hu
    _ ≤ Real.exp (|α| * T) * ‖multiply α T (sourceClass D hb hs T A - sourceClass D hb hs T B)‖ := by
      simpa only [abs_neg] using norm_multiply_le (-α) T (multiply α T (sourceClass D hb hs T A - sourceClass D hb hs T B))
    _ ≤ Real.exp (|α| * T) * (‖multiply α T (A-B)‖ / (1-q)) := mul_le_mul_of_nonneg_left hw (Real.exp_pos _).le
    _ ≤ Real.exp (|α| * T) * ((Real.exp (|α| * T) * ‖A-B‖) / (1-q)) :=
      mul_le_mul_of_nonneg_left ((div_le_div_iff_of_pos_right (sub_pos.mpr hq)).mpr (norm_multiply_le α T (A-B))) (Real.exp_pos _).le
    _ = C * ‖A-B‖ := by dsimp only [C]; ring

theorem finiteDrift_zero {Kb : ℝ≥0}
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb) (T : ℝ≥0) :
    finiteDriftPicardMap a T 0 = 0 := by
  have hd : driftVolterra (F := F) (P := P) T 0 = 0 := by
    simpa only [sub_self] using driftVolterra_sub (F := F) (P := P) T 0 0
  have hz : ∀ i : Fin N, scalarToStatePredictable (F := F) (P := P) i 0 = 0 := fun i => by
    simpa only [sub_self] using scalarToStatePredictable_sub (F := F) (P := P) i 0 0
  simp only [finiteDriftPicardMap,driftCoefficientMap,apply_zero,hd,hz,Finset.sum_const_zero]

theorem finiteNoise_zero (D : BrownianDriver N P F) {Ks : ℝ≥0}
    (a : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks) (T : ℝ≥0) :
    finiteNoisePicardMap D a T 0 = 0 := by
  have hi : ∀ j : Fin N, itoVolterra (D.brownian j) (D.coordinateStronglyMeasurable j)
      (D.filtered j) T 0 = 0 := fun j => by
    simpa only [sub_self] using itoVolterra_sub (D.brownian j) (D.coordinateStronglyMeasurable j)
      (D.filtered j) T 0 0
  have hz : ∀ i : Fin N, scalarToStatePredictable (F := F) (P := P) i 0 = 0 := fun i => by
    simpa only [sub_self] using scalarToStatePredictable_sub (F := F) (P := P) i 0 0
  simp only [finiteNoisePicardMap,stochasticCoefficientMap,apply_zero,hi,hz,Finset.sum_const_zero]

theorem sourceClass_zero (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks) (T : ℝ≥0) :
    sourceClass D a sigma T 0 = 0 := by
  have hz : (0 : PredictableStateL2 N F P) = 0 + finiteDriftPicardMap a T 0 + finiteNoisePicardMap D sigma T 0 := by
    rw [finiteDrift_zero,finiteNoise_zero,add_zero,add_zero]
  exact ((exists_unique_picard_fixedPoint D a sigma T 0).choose_spec.2 0 hz).symm

/-- The constructed linear variational state has a genuine integrated L²
bound proportional to the actual initial perturbation. -/
theorem exists_sourceClass_initial_bound (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks) (T : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ v0 : State N,
      ‖sourceClass D a sigma T (initialClass (F := F) (P := P) v0 T)‖ ≤ C * ‖v0‖ := by
  obtain ⟨K,hK⟩ := sourceClass_lipschitz D a sigma T
  refine ⟨K * PicardDependence.initialScale (P := P) T,fun v0 => ?_⟩
  have hh := hK.norm_sub_le (initialClass (F := F) (P := P) v0 T) 0
  simpa only [sourceClass_zero,sub_zero,PicardDependence.norm_initialClass,NNReal.coe_mul,mul_assoc,mul_comm,mul_left_comm] using hh

omit [IsProbabilityMeasure P] in
theorem state_norm_sq (U : PredictableStateL2 N F P) :
    ‖U‖^2 = ∫ q, ‖(U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q‖^2
      ∂nonnegativeLebesgueMeasure.prod P := by
  change ‖(U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))‖^2 = _
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  exact .of_forall (fun q => real_inner_self_eq_norm_sq _)

/-- Actual continuous adapted variational solutions and a genuine
time-integrated second-moment bound, for every initial perturbation. -/
theorem exists_strongSolution_with_secondMoment (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks) (T : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ v0 : State N, ∃ X,
      IsStrongSolutionOn a sigma D v0 X T ∧
      (∫ q, ‖(Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator
        (fun q => X q.1 q.2) q‖^2 ∂nonnegativeLebesgueMeasure.prod P) ≤ (C : ℝ)^2 * ‖v0‖^2 := by
  obtain ⟨C,hC⟩ := exists_sourceClass_initial_bound D a sigma T
  refine ⟨C,fun v0 => ?_⟩
  let U := sourceClass D a sigma T (initialClass (F := F) (P := P) v0 T)
  have hU := sourceClass_fixedPoint D a sigma T (initialClass (F := F) (P := P) v0 T)
  refine ⟨version D a sigma v0 T U,strongSolution_of_fixedPoint D a sigma v0 T U hU,?_⟩
  have he := version_timeCut_eq_fixedPoint_ae D a sigma v0 T U hU
  have hint : (∫ q, ‖(Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator
      (fun q => version D a sigma v0 T U q.1 q.2) q‖^2 ∂nonnegativeLebesgueMeasure.prod P) = ‖U‖^2 := by
    rw [state_norm_sq]
    exact integral_congr_ae (he.fun_comp (fun x : State N => ‖x‖^2))
  rw [hint]
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg U) (hC v0) 2

end SphericalAging.LinearVariationalSDE
