module

public import SphericalAging.CutoffSphere
public import SphericalAging.GlobalSDE

public section

/-! Actual predictable state classes of bounded continuous adapted states,
and pathwise uniqueness of the manuscript sphere SDE through the genuine
cutoff Picard operator. No uniqueness property is a field of solution data.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.PhysicalUniqueness
open HardSphereDynamics LocalSDE PredictableItoTime CutoffSphere
set_option maxHeartbeats 1800000
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma bounded_coordinate_timeCut_memLp (X : ℝ≥0 → Ω → State N)
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ ω ∂P, Continuous (fun s => X s ω))
    (K T : ℝ≥0) (hbound : ∀ᵐ ω ∂P, ∀ s, s ≤ T → ‖X s ω‖ ≤ K) (i : Fin N) :
    MemLp (FourPapersCommon.continuousAdaptedTimeCut (fun s ω => X s ω i) T)
      2 (nonnegativeLebesgueMeasure.prod P) := by
  have hsm := FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut F
    (fun s ω => X s ω i)
    (fun s => (CutoffSDE.coordinate_lipschitz i).continuous.comp_stronglyMeasurable (hXa s))
    (hXc.mono (fun ω hc => (CutoffSDE.coordinate_lipschitz i).continuous.comp hc)) T
  have hg := memLp_indicator_const (μ := nonnegativeLebesgueMeasure.prod P) 2
    (measurableSet_Ioc.prod MeasurableSet.univ) (K : ℝ)
    (Or.inr (FourPapersCommon.finiteMeasure_time_rectangle T))
  apply hg.mono' (hsm.mono (predictable_le_prod F))
  have hcommon := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hbound
  filter_upwards [hcommon] with q hq
  by_cases hs : q.1 ∈ Ioc (0 : ℝ≥0) T
  · rw [indicator_of_mem (show q ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨hs, mem_univ _⟩)]
    simp only [FourPapersCommon.continuousAdaptedTimeCut, hs, ite_true]
    exact (PiLp.norm_apply_le _ i).trans (hq q.1 hs.2)
  · rw [indicator_of_notMem (show q ∉ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from fun h => hs h.1)]
    simp only [FourPapersCommon.continuousAdaptedTimeCut, hs, ite_false, norm_zero]
    exact le_rfl

/-- A genuine predictable state L² class, assembled from the actual adapted
coordinate timecuts rather than postulated as additional solution data. -/
@[expose] def boundedStateClass (X : ℝ≥0 → Ω → State N)
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ ω ∂P, Continuous (fun s => X s ω))
    (K T : ℝ≥0) (hbound : ∀ᵐ ω ∂P, ∀ s, s ≤ T → ‖X s ω‖ ≤ K) : PredictableStateL2 N F P :=
  ∑ i, scalarToStatePredictable i (coefficientPredictableActual hXa hXc
    (CutoffSDE.coordinate_lipschitz i).continuous T (bounded_coordinate_timeCut_memLp X hXa hXc K T hbound i))

theorem boundedStateClass_coe (X : ℝ≥0 → Ω → State N)
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ ω ∂P, Continuous (fun s => X s ω))
    (K T : ℝ≥0) (hbound : ∀ᵐ ω ∂P, ∀ s, s ≤ T → ‖X s ω‖ ≤ K) :
    ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun q => X q.1 q.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        (boundedStateClass X hXa hXc K T hbound : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) := by
  let V (i : Fin N) := coefficientPredictableActual hXa hXc
    (CutoffSDE.coordinate_lipschitz i).continuous T (bounded_coordinate_timeCut_memLp X hXa hXc K T hbound i)
  have hsum := sumState_coeFn (fun i => scalarToStatePredictable i (V i))
  have hi := ae_all_iff.mpr (fun i => scalarToStatePredictable_coeFn i (V i))
  have hc : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P, ∀ i,
      (V i : TimeProcessL2 P) q = FourPapersCommon.continuousAdaptedTimeCut (fun s ω => X s ω i) T q := by
    apply ae_all_iff.mpr
    intro i
    exact (bounded_coordinate_timeCut_memLp X hXa hXc K T hbound i).coeFn_toLp
  filter_upwards [hsum, hi, hc] with q hsum hi hc
  change _ = ((∑ i, scalarToStatePredictable i (V i) : PredictableStateL2 N F P) :
    Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q
  rw [hsum]
  by_cases hs : q.1 ∈ Ioc (0 : ℝ≥0) T
  · rw [indicator_of_mem (show q ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨hs, mem_univ _⟩)]
    simp only [hi, hc, FourPapersCommon.continuousAdaptedTimeCut, hs, ite_true]
    exact (state_sum_basis (X q.1 q.2)).symm
  · simp only [indicator_of_notMem (show q ∉ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from fun h => hs h.1),
      hi, hc, FourPapersCommon.continuousAdaptedTimeCut, hs, ite_false, zero_smul, Finset.sum_const_zero]

omit [IsProbabilityMeasure P] in
lemma sphere_radius_bound (X : ℝ≥0 → Ω → State N) (T : ℝ≥0)
    (hSphere : ∀ᵐ ω ∂P, ∀ t, t ≤ T → OnSphere (X t ω)) :
    ∀ᵐ ω ∂P, ∀ t, t ≤ T → ‖X t ω‖ ≤ (N + 1 : ℝ≥0) := by
  filter_upwards [hSphere] with ω hω
  intro t ht
  have hsq := (onSphere_iff_norm_sq (X t ω)).mp (hω t ht)
  simp only [NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
  nlinarith [norm_nonneg (X t ω), Nat.cast_nonneg (α := ℝ) N, sq_nonneg (N : ℝ)]

/-- An actual physical sphere solution satisfies the actual globally
Lipschitz cutoff SDE, using equality of coefficients on the proved common
sphere path event. -/
theorem cutoff_solution_of_physical (D : BrownianDriver N P F) (β : ℝ)
    (J : FiniteModel.Disorder N p) (x0 : State N) (X : ℝ≥0 → Ω → State N) (T : ℝ≥0)
    (hsol : IsLocalStrongSolutionOn (fun i x => hamiltonianDrift β J x i) (fun i j x => noiseColumn x j i)
      physical_noise_continuous D x0 X T)
    (hSphere : ∀ᵐ ω ∂P, ∀ t, t ≤ T → OnSphere (X t ω))
    (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) ≤ (R : ℝ)^2)
    (hsigma : ∀ i j, Continuous (CutoffSDE.cutoffNoise N R hR i j)) :
    IsLocalStrongSolutionOn (CutoffSDE.cutoffDrift β J R hR) (CutoffSDE.cutoffNoise N R hR)
      hsigma D x0 X T := by
  have hbound : ∀ᵐ ω ∂P, ∀ t, t ≤ T → ‖X t ω‖ ≤ R := by
    filter_upwards [hSphere] with ω hω
    intro t ht
    have hsq := (onSphere_iff_norm_sq (X t ω)).mp (hω t ht)
    nlinarith [norm_nonneg (X t ω), R.coe_nonneg]
  apply coefficient_congr_onPath hsigma hsol
  · intro i
    filter_upwards [hbound] with ω hω
    intro t ht
    exact CutoffSDE.cutoffDrift_eq β J R hR _ (hω t ht) i
  · intro i j
    filter_upwards [hbound] with ω hω
    intro t ht
    exact CutoffSDE.cutoffNoise_eq N R hR _ (hω t ht) i j

/-- Pathwise uniqueness of the actual finite-N Hamiltonian sphere SDE on
any finite horizon. Both solution premises contain the actual full
filtration matrix Itô equation; their state classes and the uniqueness
argument are constructed from the genuine sphere bound. -/
theorem physical_pathwise_uniqueness (D : BrownianDriver N P F) (β : ℝ)
    (J : FiniteModel.Disorder N p) (x0 : State N) (T : ℝ≥0)
    (X Y : ℝ≥0 → Ω → State N)
    (hX : IsLocalStrongSolutionOn (fun i x => hamiltonianDrift β J x i) (fun i j x => noiseColumn x j i)
      physical_noise_continuous D x0 X T)
    (hY : IsLocalStrongSolutionOn (fun i x => hamiltonianDrift β J x i) (fun i j x => noiseColumn x j i)
      physical_noise_continuous D x0 Y T)
    (hXs : ∀ᵐ ω ∂P, ∀ t, t ≤ T → OnSphere (X t ω))
    (hYs : ∀ᵐ ω ∂P, ∀ t, t ≤ T → OnSphere (Y t ω)) :
    ∀ᵐ ω ∂P, ∀ t, t ≤ T → X t ω = Y t ω := by
  let R : ℝ≥0 := N + 1
  have hR : 0 < (R : ℝ) := by simp only [R, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]; positivity
  have hNR : (N : ℝ) ≤ (R : ℝ)^2 := by
    simp only [R, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
    nlinarith [sq_nonneg (N : ℝ), Nat.cast_nonneg (α := ℝ) N]
  obtain ⟨Kb, hb⟩ := CutoffSDE.cutoffDrift_lipschitz β J R hR
  obtain ⟨Ks, hsigma⟩ := CutoffSDE.cutoffNoise_lipschitz N R hR
  have hXcut := cutoff_solution_of_physical D β J x0 X T hX hXs R hR hNR (fun i j => (hsigma i j).continuous)
  have hYcut := cutoff_solution_of_physical D β J x0 Y T hY hYs R hR hNR (fun i j => (hsigma i j).continuous)
  obtain ⟨hXa, hXc, hbmX, hsmX, hEqX⟩ := hX
  obtain ⟨hYa, hYc, hbmY, hsmY, hEqY⟩ := hY
  exact GlobalSDE.strongSolution_unique_of_stateClasses D hb hsigma x0 T
    (boundedStateClass_coe X hXa hXc R T (sphere_radius_bound X T hXs))
    (boundedStateClass_coe Y hYa hYc R T (sphere_radius_bound Y T hYs)) hXcut hYcut

/-- On a common Brownian driver, two actual global sphere solutions agree
simultaneously for every time. Countability of integer horizons supplies
one common null event, rather than a separate exceptional event per time. -/
theorem physical_global_pathwise_uniqueness (D : BrownianDriver N P F) (β : ℝ)
    (J : FiniteModel.Disorder N p) (x0 : State N) (X Y : ℝ≥0 → Ω → State N)
    (hX : ∀ T, IsLocalStrongSolutionOn (fun i x => hamiltonianDrift β J x i) (fun i j x => noiseColumn x j i)
      physical_noise_continuous D x0 X T)
    (hY : ∀ T, IsLocalStrongSolutionOn (fun i x => hamiltonianDrift β J x i) (fun i j x => noiseColumn x j i)
      physical_noise_continuous D x0 Y T)
    (hXs : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω))
    (hYs : ∀ᵐ ω ∂P, ∀ t, OnSphere (Y t ω)) :
    ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω := by
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ t, t ≤ (n : ℝ≥0) → X t ω = Y t ω := by
    apply ae_all_iff.mpr
    intro n
    exact physical_pathwise_uniqueness D β J x0 n X Y (hX n) (hY n)
      (hXs.mono (fun ω hω t _ => hω t)) (hYs.mono (fun ω hω t _ => hω t))
  filter_upwards [hall] with ω hω
  intro t
  obtain ⟨n, hn⟩ := exists_nat_ge t
  exact hω n t hn

end SphericalAging.PhysicalUniqueness
