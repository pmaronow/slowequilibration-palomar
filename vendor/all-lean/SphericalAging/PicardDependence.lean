module

public import SphericalAging.PhysicalUniqueness

public section

/-! Quantitative dependence of the actual finite-driver predictable Picard
fixed point on its source class. Subsequent parameter statements apply to
the actual Hamiltonian coefficient family, rather than assumed flows.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.PicardDependence
open HardSphereDynamics LocalSDE PredictableItoTime PredictableDriftTime
open WeightedPredictable WeightedPicard
set_option maxHeartbeats 1800000
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def sourceClass (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hs : ∀ i j, LipschitzWith Ks (sigma i j))
    (T : ℝ≥0) (A : PredictableStateL2 N F P) : PredictableStateL2 N F P :=
  (GlobalSDE.exists_unique_picard_fixedPoint D hb hs T A).choose

lemma sourceClass_fixedPoint (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hs : ∀ i j, LipschitzWith Ks (sigma i j))
    (T : ℝ≥0) (A : PredictableStateL2 N F P) :
    sourceClass D hb hs T A = A + finiteDriftPicardMap hb T (sourceClass D hb hs T A) +
      finiteNoisePicardMap D hs T (sourceClass D hb hs T A) :=
  (GlobalSDE.exists_unique_picard_fixedPoint D hb hs T A).choose_spec.1

lemma weighted_sourceClass_sub_bound (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hs : ∀ i j, LipschitzWith Ks (sigma i j))
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
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hs : ∀ i j, LipschitzWith Ks (sigma i j))
    (T : ℝ≥0) : ∃ K : ℝ≥0, LipschitzWith K (sourceClass D hb hs T) := by
  obtain ⟨α, hα, Cd, Ci, hCd, hCi, hsmall⟩ := exists_contraction_parameters N Kb Ks T
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

lemma initialClass_sub (T : ℝ≥0) (x y : State N) :
    initialClass (F := F) (P := P) (x-y) T = initialClass x T - initialClass y T := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [initialClass_coeFn (F := F) (P := P) (x-y) T,
    initialClass_coeFn (F := F) (P := P) x T, initialClass_coeFn (F := F) (P := P) y T,
    Lp.coeFn_sub (initialClass (F := F) (P := P) x T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
      (initialClass (F := F) (P := P) y T)] with q hxy hx hy hsub
  change (initialClass (F := F) (P := P) (x-y) T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q =
    ((initialClass (F := F) (P := P) x T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) -
      (initialClass (F := F) (P := P) y T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))) q
  rw [hsub]
  simp only [Pi.sub_apply, hxy, hx, hy]
  by_cases hq : q ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) <;> simp [hq]

@[expose] def initialScale (T : ℝ≥0) : ℝ≥0 :=
  ((nonnegativeLebesgueMeasure.prod P) (Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)) ^ (1 / (2 : ℝ))).toNNReal

lemma norm_initialClass (T : ℝ≥0) (x : State N) :
    ‖initialClass (F := F) (P := P) x T‖ = ‖x‖ * (initialScale (P := P) T : ℝ) := by
  change ‖(initialClass (F := F) (P := P) x T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))‖ = _
  rw [Lp.norm_def, eLpNorm_congr_ae (initialClass_coeFn (F := F) (P := P) x T),
    eLpNorm_indicator_const (measurableSet_Ioc.prod MeasurableSet.univ).nullMeasurableSet (by norm_num) (by norm_num),
    ENNReal.toReal_mul, toReal_enorm]
  congr 1

/-- The actual deterministic initial state embedding is Lipschitz into the
predictable product L² state space. -/
theorem initialClass_lipschitz (T : ℝ≥0) :
    LipschitzWith (initialScale (P := P) T) (fun x : State N => initialClass (F := F) (P := P) x T) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm]
  rw [← initialClass_sub, norm_initialClass, mul_comm]

/-- For fixed actual globally Lipschitz coefficients and full Brownian
filtration, the genuine solution class depends continuously on the
initial state. This is the actual class used by the constructed SDE. -/
theorem horizonClass_lipschitz_initial (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hs : ∀ i j, LipschitzWith Ks (sigma i j))
    (T : ℝ≥0) : ∃ K : ℝ≥0, LipschitzWith K (fun x : State N => GlobalSDE.horizonClass D hb hs x T) := by
  obtain ⟨K, hK⟩ := sourceClass_lipschitz D hb hs T
  have heq : (fun x : State N => GlobalSDE.horizonClass D hb hs x T) =
      (sourceClass D hb hs T) ∘ (fun x : State N => initialClass (F := F) (P := P) x T) := rfl
  rw [heq]
  exact ⟨K * initialScale (P := P) T, hK.comp (initialClass_lipschitz T)⟩

end SphericalAging.PicardDependence
