module

public import SphericalAging.WeightedPredictable

public section

/-! Exponentially transformed Picard iteration for the actual finite-driver
strong SDE. The kernel operator estimates are separate mathematical lemmas;
this module combines them with the actual coefficient Nemytskii maps. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.WeightedPicard
open HardSphereDynamics PredictableItoTime PredictableDriftTime WeightedPredictable
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem norm_weighted_driftCoefficient_sub_le {Kb : ℝ≥0} {b : State N → ℝ}
    (hb : LipschitzWith Kb b) (α : ℝ) (T : ℝ≥0) (Cd : ℝ≥0)
    (hd : ∀ A : PredictableProcessL2 F P,
      ‖multiply α T (driftVolterra T A)‖ ≤ Cd * ‖multiply α T A‖)
    (U V : PredictableStateL2 N F P) :
    ‖multiply α T (driftCoefficientMap hb T U - driftCoefficientMap hb T V)‖ ≤
      (Cd : ℝ) * Kb * ‖multiply α T (U-V)‖ := by
  unfold driftCoefficientMap
  rw [← driftVolterra_sub]
  calc
    _ ≤ (Cd : ℝ) * ‖multiply α T (predictableCoefficient hb U T - predictableCoefficient hb V T)‖ := hd _
    _ ≤ (Cd : ℝ) * ((Kb : ℝ) * ‖multiply α T (U-V)‖) :=
      mul_le_mul_of_nonneg_left (norm_weighted_coefficient_sub_le hb α T U V) Cd.coe_nonneg
    _ = _ := by ring

theorem norm_weighted_stochasticCoefficient_sub_le (D : BrownianDriver N P F) (j : Fin N)
    {Ks : ℝ≥0} {sigma : State N → ℝ} (hs : LipschitzWith Ks sigma)
    (α : ℝ) (T : ℝ≥0) (Ci : ℝ≥0)
    (hi : ∀ A : PredictableProcessL2 F P,
      ‖multiply α T (itoVolterra (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) T A)‖ ≤
        Ci * ‖multiply α T A‖) (U V : PredictableStateL2 N F P) :
    ‖multiply α T (stochasticCoefficientMap D j hs T U - stochasticCoefficientMap D j hs T V)‖ ≤
      (Ci : ℝ) * Ks * ‖multiply α T (U-V)‖ := by
  unfold stochasticCoefficientMap
  rw [← itoVolterra_sub]
  calc
    _ ≤ (Ci : ℝ) * ‖multiply α T (predictableCoefficient hs U T - predictableCoefficient hs V T)‖ := hi _
    _ ≤ (Ci : ℝ) * ((Ks : ℝ) * ‖multiply α T (U-V)‖) :=
      mul_le_mul_of_nonneg_left (norm_weighted_coefficient_sub_le hs α T U V) Ci.coe_nonneg
    _ = _ := by ring

theorem norm_weighted_finiteDrift_sub_le {Kb : ℝ≥0} {b : Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (α : ℝ) (T : ℝ≥0) (Cd : ℝ≥0)
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
    {Ks : ℝ≥0} {sigma : Fin N → Fin N → State N → ℝ}
    (hs : ∀ i j, LipschitzWith Ks (sigma i j)) (α : ℝ) (T : ℝ≥0) (Ci : ℝ≥0)
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
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hs : ∀ i j, LipschitzWith Ks (sigma i j))
    (α : ℝ) (T : ℝ≥0) (A U : PredictableStateL2 N F P) : PredictableStateL2 N F P :=
  multiply α T (A + finiteDriftPicardMap hb T (multiply (-α) T U) +
    finiteNoisePicardMap D hs T (multiply (-α) T U))

/-- Genuine Banach construction for the transformed full SDE Picard map.
The scalar operator norm lemmas are subsequently instantiated by the proved
weighted kernel estimates. -/
theorem exists_unique_picard_fixedPoint_of_operator_bounds (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hs : ∀ i j, LipschitzWith Ks (sigma i j))
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

/-- Positive exponential rates giving a strict contraction exist for every
finite horizon and every pair of finite coefficient Lipschitz constants. -/
theorem exists_contraction_parameters (N : ℕ) (Kb Ks T : ℝ≥0) :
    ∃ α : ℝ, 0 < α ∧ ∃ Cd Ci : ℝ≥0,
      (Cd : ℝ) = Real.sqrt ((T : ℝ) / (2*α)) ∧
      (Ci : ℝ) = Real.sqrt (1 / (2*α)) ∧
      (N : ℝ≥0) * Cd * Kb + (N : ℝ≥0)^2 * Ci * Ks < 1 := by
  let c : ℝ≥0 := (N : ℝ≥0) * NNReal.sqrt T * Kb + (N : ℝ≥0)^2 * Ks
  let d : ℝ≥0 := 1+c
  have hd : 0 < d := by dsimp only [d]; positivity
  have hdr : 0 < (d : ℝ) := hd
  let α : ℝ := (d : ℝ)^2 / 2
  let Cd : ℝ≥0 := NNReal.sqrt T / d
  let Ci : ℝ≥0 := 1/d
  have hα : 0 < α := by dsimp only [α]; positivity
  have hden : 2*α = (d : ℝ)^2 := by dsimp only [α]; ring
  have hCd : (Cd : ℝ) = Real.sqrt ((T : ℝ)/(2*α)) := by
    rw [hden, Real.sqrt_div T.coe_nonneg, Real.sqrt_sq_eq_abs, abs_of_pos hdr]
    simp only [Cd, NNReal.coe_div, Real.coe_sqrt]
  have hCi : (Ci : ℝ) = Real.sqrt (1/(2*α)) := by
    rw [hden, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_sq_eq_abs, abs_of_pos hdr, Real.sqrt_one]
    simp only [Ci, NNReal.coe_div, NNReal.coe_one]
  refine ⟨α, hα, Cd, Ci, hCd, hCi, ?_⟩
  calc
    _ = c/d := by dsimp only [Cd, Ci, c]; field_simp
    _ < 1 := (div_lt_one hd).mpr (by dsimp only [d]; simp)

/-- A fixed point of the genuine predictable SDE map produces the actual
strong integral equation on the specified horizon. -/
theorem strongSolution_of_picard_fixedPoint (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) (T : ℝ≥0) (U : PredictableStateL2 N F P)
    (hU : U = LocalSDE.initialClass (F := F) (P := P) x0 T +
      finiteDriftPicardMap hb T U + finiteNoisePicardMap D hsigma T U) :
    LocalSDE.IsLocalStrongSolutionOn b sigma (fun i j => (hsigma i j).continuous) D x0
      (LocalSDE.version D hb hsigma x0 T U) T := by
  have hXa := LocalSDE.version_stronglyAdapted D hb hsigma x0 T U
  have hXc := LocalSDE.version_ae_continuous D hb hsigma x0 T U
  have hXeq := LocalSDE.version_timeCut_eq_fixedPoint_ae D hb hsigma x0 T U hU
  refine ⟨hXa, hXc, (fun i => LocalSDE.coefficient_timeCut_memLp hXeq (hb i) T le_rfl),
    (fun i j t ht => LocalSDE.coefficient_timeCut_memLp hXeq (hsigma i j) t ht), ?_⟩
  intro t ht i
  filter_upwards [LocalSDE.driftVersion_eq_actual_drift_ae hXeq (hb i),
    LocalSDE.actual_driverIto_ae_eq hXeq hXa hXc D (hsigma i) t ht] with omega hbactual hsactual
  rw [LocalSDE.version_apply, hsactual]
  simp only [LocalSDE.coordinateVersion, hbactual t ht]

end SphericalAging.WeightedPicard
