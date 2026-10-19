module

public import SphericalAging.RadialProcess
public import SphericalAging.RadialUniqueness
public import SphericalAging.CutoffSDE

public section

/-! Radius preservation for a genuinely bounded, stopped physical SDE.
The radial equation is derived from the actual matrix SDE, the true Itô
operator and the proved radius factorization. It is not assumed in the
solution data. Unstopping and existence are separate subsequent claims.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.SpherePreservation
open HardSphereDynamics VectorIto RadialProcess RadialItoRepresentation StoppedVectorIto
set_option maxHeartbeats 1800000

@[expose] def radialDriftFactor {N : ℕ} (β : ℝ) (gradient : State N → State N) (x : State N) : ℝ :=
  -2 * β * ⟪x, gradient x⟫_ℝ / N + 2 * ⟪x,x⟫_ℝ / (N : ℝ)^2 - 2

@[expose] def radialNoiseFactor {N : ℕ} (x : State N) (i : Fin N) : ℝ := -2 * Real.sqrt 2 * x i / N

lemma continuous_radialDriftFactor {N : ℕ} (β : ℝ) (gradient : State N → State N)
    (hgradient : Continuous gradient) : Continuous (radialDriftFactor β gradient) := by
  unfold radialDriftFactor
  fun_prop

lemma continuous_radialNoiseFactor {N : ℕ} (i : Fin N) :
    Continuous (fun x : State N => radialNoiseFactor x i) := by
  unfold radialNoiseFactor
  fun_prop

theorem scalar_bound_on_ball {N : ℕ} (f : State N → ℝ) (hf : Continuous f) (R : ℝ≥0) :
    ∃ K : ℝ≥0, ∀ x, ‖x‖ ≤ R → ‖f x‖ ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : State N) (R : ℝ)).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨⟨max K 0, le_max_right _ _⟩, fun x hx => ?_⟩
  have hmem : x ∈ Metric.closedBall (0 : State N) (R : ℝ) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  exact (hK x hmem).trans (le_max_left _ _)

lemma sum_two_coordinates {N : ℕ} (x y : State N) :
    (∑ k : Fin N, 2 * x k * y k) = 2 * ⟪x,y⟫_ℝ := by
  rw [PiLp.inner_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [RCLike.inner_apply, conj_trivial]
  ring

lemma radialGenerator_coordinates {N : ℕ} (β : ℝ) (gradient : State N → State N) (x : State N) :
    radialGenerator β gradient x =
      (∑ k : Fin N, 2 * x k * (drift β gradient x) k) +
        ∑ k : Fin N, ∑ i : Fin N, (noiseColumn x i k)^2 := by
  rw [radialGenerator, ← sum_two_coordinates]
  congr 1
  unfold noiseQuadraticTrace
  simp_rw [← coordinate_square_sum]
  exact Finset.sum_comm

lemma radialGenerator_scaled_coordinates {N : ℕ} (β : ℝ) (gradient : State N → State N)
    (x : State N) (c : ℝ) (hc : c^2 = c) :
    (∑ k : Fin N, 2 * x k * (c * (drift β gradient x) k)) +
      (∑ k : Fin N, ∑ i : Fin N, (c * noiseColumn x i k)^2) = c * radialGenerator β gradient x := by
  rw [radialGenerator_coordinates, mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    ring
  · apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow, hc]

variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def coordinates (Y : ℝ≥0 → Ω → State N) : Fin N → ℝ≥0 → Ω → ℝ := fun k s ω => Y s ω k

lemma coordinates_adapted {Y : ℝ≥0 → Ω → State N} (hY : StronglyAdapted 𝓕 Y) :
    ∀ k, StronglyAdapted 𝓕 (coordinates Y k) := by
  intro k s
  exact ((CutoffSDE.coordinate_lipschitz k).continuous.measurable.comp (hY s).measurable).stronglyMeasurable

omit [IsProbabilityMeasure P] in
lemma coordinates_continuous {Y : ℝ≥0 → Ω → State N}
    (hY : ∀ ω, Continuous (fun s => Y s ω)) :
    ∀ k, ∀ᵐ ω ∂P, Continuous (fun s => coordinates Y k s ω) := by
  intro k
  exact .of_forall (fun ω => (CutoffSDE.coordinate_lipschitz k).continuous.comp (hY ω))

omit [MeasurableSpace Ω] in
lemma coordinates_bound {Y : ℝ≥0 → Ω → State N} {R : ℝ≥0}
    (hY : ∀ s ω, ‖Y s ω‖ ≤ R) : ∀ k s ω, ‖coordinates Y k s ω‖ ≤ R :=
  fun k s ω => (PiLp.norm_apply_le (Y s ω) k).trans (hY s ω)

@[expose] def stoppedPhysicalDrift (β : ℝ) (gradient : State N → State N) (Y : ℝ≥0 → Ω → State N)
    (τ : Ω → ℝ≥0) (T : ℝ≥0) : Fin N → ℝ≥0 → Ω → ℝ :=
  fun k s ω => stoppedTimeCoefficient τ T (s, ω) * (drift β gradient (Y s ω)) k

omit [MeasurableSpace Ω] in
lemma stoppedTimeCoefficient_sq (τ : Ω → ℝ≥0) (T : ℝ≥0) (p : ℝ≥0 × Ω) :
    stoppedTimeCoefficient τ T p ^ 2 = stoppedTimeCoefficient τ T p := by
  unfold stoppedTimeCoefficient
  split_ifs <;> norm_num

lemma continuous_physical_drift (β : ℝ) (gradient : State N → State N)
    (hgradient : Continuous gradient) : Continuous (drift β gradient) := by
  unfold drift projection
  fun_prop

lemma stoppedPhysicalDrift_measurable (β : ℝ) (gradient : State N → State N)
    (hgradient : Continuous gradient) (Y : ℝ≥0 → Ω → State N)
    (hYa : StronglyAdapted 𝓕 Y) (hYc : ∀ ω, Continuous (fun s => Y s ω))
    (τ : Ω → ℝ≥0) (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (k : Fin N) : Measurable (Function.uncurry (stoppedPhysicalDrift β gradient Y τ T k)) := by
  have hYm : StronglyMeasurable (Function.uncurry Y) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hYc
      (fun s => (hYa s).mono (𝓕.le s))
  exact ((stronglyMeasurable_stoppedTimeCoefficient hτ T).mono
    (predictable_le_prod 𝓕)).measurable.mul
      (((CutoffSDE.coordinate_lipschitz k).continuous.comp
        (continuous_physical_drift β gradient hgradient)).measurable.comp hYm.measurable)

omit [MeasurableSpace Ω] in
lemma stoppedPhysicalDrift_integrable (β : ℝ) (gradient : State N → State N)
    (hgradient : Continuous gradient) (Y : ℝ≥0 → Ω → State N)
    (hYc : ∀ ω, Continuous (fun s => Y s ω)) (R : ℝ≥0)
    (hYbound : ∀ s ω, ‖Y s ω‖ ≤ R) (τ : Ω → ℝ≥0) (T : ℝ≥0) :
    ∀ k t ω, IntegrableOn (fun s => stoppedPhysicalDrift β gradient Y τ T k s ω)
      (Ioc 0 t) nonnegativeLebesgueMeasure := by
  intro k t ω
  obtain ⟨C, hC⟩ := scalar_bound_on_ball
    (fun x => (drift β gradient x) k)
    ((CutoffSDE.coordinate_lipschitz k).continuous.comp
      (continuous_physical_drift β gradient hgradient)) R
  have hsm : StronglyMeasurable (fun s => stoppedPhysicalDrift β gradient Y τ T k s ω) := by
    unfold stoppedPhysicalDrift stoppedTimeCoefficient
    simp only [ite_mul, one_mul, zero_mul]
    exact StronglyMeasurable.ite
      (show MeasurableSet {s : ℝ≥0 | s ∈ Ioc 0 T ∧ s ≤ τ ω} from
        measurableSet_Ioc.inter measurableSet_Iic)
      (((CutoffSDE.coordinate_lipschitz k).continuous.comp
        (continuous_physical_drift β gradient hgradient)).comp (hYc ω)).stronglyMeasurable
      stronglyMeasurable_const
  change Integrable _ (FourPapersCommon.FilteredBrownian.finiteTimeMeasure t)
  apply (memLp_one_iff_integrable).mp
  apply MemLp.of_bound hsm.aestronglyMeasurable (C : ℝ)
  exact .of_forall (fun s => by
    change ‖stoppedTimeCoefficient τ T (s, ω) * (drift β gradient (Y s ω)) k‖ ≤ C
    rw [norm_mul]
    calc
      _ ≤ 1 * (C : ℝ) := mul_le_mul (stoppedTimeCoefficient_bound τ T (s, ω))
        (hC _ (hYbound s ω)) (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _)

/-- The defect process of a bounded actual state is adapted and continuous;
its uniform bound uses the actual Euclidean norm. -/
@[expose] def defectProcess (Y : ℝ≥0 → Ω → State N) : ℝ≥0 → Ω → ℝ := fun s ω => radiusDefect (Y s ω)

lemma continuous_radiusDefect : Continuous (radiusDefect (N := N)) := by
  unfold radiusDefect
  fun_prop

lemma defect_adapted {Y : ℝ≥0 → Ω → State N} (hY : StronglyAdapted 𝓕 Y) :
    StronglyAdapted 𝓕 (defectProcess Y) := fun s =>
  (continuous_radiusDefect.measurable.comp (hY s).measurable).stronglyMeasurable

omit [IsProbabilityMeasure P] in
lemma defect_continuous {Y : ℝ≥0 → Ω → State N}
    (hY : ∀ ω, Continuous (fun s => Y s ω)) :
    ∀ᵐ ω ∂P, Continuous (fun s => defectProcess Y s ω) :=
  .of_forall (fun ω => continuous_radiusDefect.comp (hY ω))

omit [MeasurableSpace Ω] in
lemma defect_bound {Y : ℝ≥0 → Ω → State N} (R : ℝ≥0)
    (hY : ∀ s ω, ‖Y s ω‖ ≤ R) : ∀ s ω, ‖defectProcess Y s ω‖ ≤ (R : ℝ)^2 + N := by
  intro s ω
  rw [defectProcess, radiusDefect_eq_norm_sq_sub]
  calc
    ‖‖Y s ω‖ ^ 2 - N‖ ≤ ‖‖Y s ω‖ ^ 2‖ + ‖(N : ℝ)‖ := norm_sub_le _ _
    _ = ‖Y s ω‖ ^ 2 + N := by rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ _ := add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hY s ω) 2) le_rfl

/-- Sphere preservation for a bounded stopped physical SDE, with its actual
matrix drift and noise classes. The only SDE premise is the matrix integral
equation: the radial equation and its zero solution are derived here. -/
theorem bounded_stopped_physical_solution_onSphere (hN : N ≠ 0)
    (D : BrownianDriver N P 𝓕) (β : ℝ) (gradient : State N → State N)
    (hgradient : Continuous gradient) (Y : ℝ≥0 → Ω → State N)
    (hYa : StronglyAdapted 𝓕 Y) (hYc : ∀ ω, Continuous (fun s => Y s ω))
    (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hYbound : ∀ s ω, ‖Y s ω‖ ≤ R)
    (τ : Ω → ℝ≥0) (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0))) (T : ℝ≥0)
    (A : Fin N → PredictableProcessL2 𝓕 P) (U : Fin N → Fin N → PredictableProcessL2 𝓕 P)
    (hA : ∀ k, (A k : ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun p => stoppedPhysicalDrift β gradient Y τ T k p.1 p.2)
    (hU : ∀ k i, (U k i : ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun p => stoppedTimeCoefficient τ T p * noiseColumn (Y p.1 p.2) i k)
    (hinitial : ∀ᵐ ω ∂P, OnSphere (Y 0 ω))
    (heq : ∀ k s, coordinates Y k s =ᵐ[P] fun ω => coordinates Y k 0 ω +
      integratedDrift (stoppedPhysicalDrift β gradient Y τ T k) s ω + vectorProcess D (U k) s ω) :
    ∀ᵐ ω ∂P, ∀ t, t ≤ T → OnSphere (Y t ω) := by
  let X := coordinates Y
  have hXa := coordinates_adapted hYa
  have hXc := coordinates_continuous (P := P) hYc
  have hXbound := coordinates_bound hYbound
  obtain ⟨S, hS⟩ := CutoffSDE.cutoffNoise_bounded N (R : ℝ) hR
  have hUb : ∀ k i, ∀ᵐ p ∂nonnegativeLebesgueMeasure.prod P,
      ‖(U k i : ℝ≥0 × Ω → ℝ) p‖ ≤ S := by
    intro k i
    filter_upwards [hU k i] with p hp
    rw [hp, norm_mul]
    have hnoise : ‖noiseColumn (Y p.1 p.2) i k‖ ≤ S := by
      rw [← CutoffSDE.cutoffNoise_eq N (R : ℝ) hR _ (hYbound p.1 p.2) k i]
      exact hS k i _
    calc
      _ ≤ 1 * (S : ℝ) := mul_le_mul (stoppedTimeCoefficient_bound τ T p) hnoise
        (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  let B := radialDrift A U X hXa hXc R hXbound S hUb T
  let V := radialNoise U X hXa hXc R hXbound T
  let Z := defectProcess Y
  obtain ⟨M, hM⟩ := scalar_bound_on_ball (radialDriftFactor β gradient)
    (continuous_radialDriftFactor β gradient hgradient) R
  have hKi : ∀ i : Fin N, ∃ K : ℝ≥0, ∀ x, ‖x‖ ≤ R → ‖radialNoiseFactor x i‖ ≤ K :=
    fun i => scalar_bound_on_ball (fun x => radialNoiseFactor x i) (continuous_radialNoiseFactor i) R
  let Ki : Fin N → ℝ≥0 := fun i => Classical.choose (hKi i)
  let K : ℝ≥0 := ∑ i, Ki i
  have hK : ∀ (i : Fin N) (x : State N), ‖x‖ ≤ R → ‖radialNoiseFactor x i‖ ≤ K := by
    intro i x hx
    have hi : Ki i ≤ K := Finset.single_le_sum (fun j _ => (zero_le : 0 ≤ Ki j)) (Finset.mem_univ i)
    exact (Classical.choose_spec (hKi i) x hx).trans (NNReal.coe_le_coe.mpr hi)
  have hallA := ae_all_iff.mpr hA
  have hallU := ae_all_iff.mpr (fun k => ae_all_iff.mpr (hU k))
  have hB : ∀ᵐ p ∂nonnegativeLebesgueMeasure.prod P, p.1 ∈ Ioc 0 T →
      ‖(B : TimeProcessL2 P) p‖ ≤ (M : ℝ) * ‖Z p.1 p.2‖ := by
    filter_upwards [radialDrift_coe A U X hXa hXc R hXbound S hUb T, hallA, hallU]
      with p hb ha hu
    intro hp
    change ‖(B : ℝ≥0 × Ω → ℝ) p‖ ≤ _
    rw [hb]
    simp only [FourPapersCommon.continuousAdaptedTimeCut, hp, ite_true, twiceState,
      ha, hu, X, coordinates, stoppedPhysicalDrift]
    rw [radialGenerator_scaled_coordinates β gradient _ _ (stoppedTimeCoefficient_sq τ T p),
      radialGenerator_factor hN]
    change ‖stoppedTimeCoefficient τ T p * (radiusDefect (Y p.1 p.2) * radialDriftFactor β gradient (Y p.1 p.2))‖ ≤ _
    rw [norm_mul, norm_mul]
    calc
      _ ≤ 1 * (‖radiusDefect (Y p.1 p.2)‖ * (M : ℝ)) := mul_le_mul
        (stoppedTimeCoefficient_bound τ T p) (mul_le_mul_of_nonneg_left (hM _ (hYbound p.1 p.2)) (norm_nonneg _))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
      _ = _ := by simp only [one_mul, Z, defectProcess]; ring
  have hV : ∀ i, ∀ᵐ p ∂nonnegativeLebesgueMeasure.prod P, p.1 ∈ Ioc 0 T →
      ‖(V i : TimeProcessL2 P) p‖ ≤ (K : ℝ) * ‖Z p.1 p.2‖ := by
    intro i
    filter_upwards [radialNoise_coe U X hXa hXc R hXbound T i, hallU] with p hv hu
    intro hp
    change ‖(V i : ℝ≥0 × Ω → ℝ) p‖ ≤ _
    rw [hv]
    simp only [FourPapersCommon.continuousAdaptedTimeCut, hp, ite_true, twiceState, hu, X, coordinates]
    have hsum : (∑ k, 2 * Y p.1 p.2 k * (stoppedTimeCoefficient τ T p * noiseColumn (Y p.1 p.2) i k)) =
        stoppedTimeCoefficient τ T p * (2 * ⟪Y p.1 p.2, noiseColumn (Y p.1 p.2) i⟫_ℝ) := by
      rw [← sum_two_coordinates, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hsum, radialNoise_factor hN]
    change ‖stoppedTimeCoefficient τ T p * (radiusDefect (Y p.1 p.2) * radialNoiseFactor (Y p.1 p.2) i)‖ ≤ _
    rw [norm_mul, norm_mul]
    calc
      _ ≤ 1 * (‖radiusDefect (Y p.1 p.2)‖ * (K : ℝ)) := mul_le_mul
        (stoppedTimeCoefficient_bound τ T p) (mul_le_mul_of_nonneg_left (hK i _ (hYbound p.1 p.2)) (norm_nonneg _))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
      _ = _ := by simp only [one_mul, Z, defectProcess]; ring
  have hzeroInitial : ∀ᵐ ω ∂P, (∑ k, X k 0 ω ^ 2) = (N : ℝ) := by
    filter_upwards [hinitial] with ω hω
    simpa only [X, coordinates, coordinate_square_sum, OnSphere] using hω
  have hZE : ∀ t, t ≤ T → ∀ᵐ ω ∂P, Z t ω = PredictableDriftTime.driftVersion B t t ω +
      (vectorProcessLp D V t : Ω → ℝ) ω := by
    intro t ht
    have h := zero_initial_radius_class_equation D A U X
      (stoppedPhysicalDrift β gradient Y τ T) hXa hXc R hXbound S hUb T t ht N hzeroInitial hA
      (stoppedPhysicalDrift_measurable β gradient hgradient Y hYa hYc τ hτ T)
      (fun k s => .of_forall (stoppedPhysicalDrift_integrable β gradient hgradient Y hYc R hYbound τ T k s)) heq
    filter_upwards [h] with ω hω
    simpa only [X, coordinates, coordinate_square_sum, Z, defectProcess, radiusDefect, B, V] using hω
  have hZb : ∀ᵐ ω ∂P, ∀ t, ‖Z t ω‖ ≤ (R^2 + N : ℝ≥0) :=
    .of_forall (fun ω t => by simpa only [NNReal.coe_add, NNReal.coe_pow, NNReal.coe_natCast] using defect_bound R hYbound t ω)
  have hzero := RadialUniqueness.bounded_linear_equation_zero D Z (defect_adapted hYa)
    (defect_continuous (P := P) hYc) (R^2 + N) M K hZb T B V hB hV hZE
  filter_upwards [hzero] with ω hω
  intro t ht
  have hz := hω t ht
  change radiusDefect (Y t ω) = 0 at hz
  unfold radiusDefect at hz
  exact sub_eq_zero.mp hz

end SphericalAging.SpherePreservation
