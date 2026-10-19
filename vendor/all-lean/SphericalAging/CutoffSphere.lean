module

public import SphericalAging.SpherePreservation
public import SphericalAging.AllPathSDE
public import SphericalAging.ClosedHitStopping

public section

/-! The actual Hamiltonian cutoff strong solution cannot exit any ball
strictly containing its initial sphere. This instantiates the proved
stopped matrix Itô representation; sphere invariance is not assumed.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.CutoffSphere
open HardSphereDynamics LocalSDE VectorIto SpherePreservation StoppedVectorIto
open ClosedHitStopping StoppedSDE RadialItoRepresentation WeightedDriftSums
set_option maxHeartbeats 2200000
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma coefficientPredictableActual_timeRestrict {X : ℝ≥0 → Ω → State N}
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ ω ∂P, Continuous (fun s => X s ω))
    {g : State N → ℝ} (hg : Continuous g) (T t : ℝ≥0) (ht : t ≤ T)
    (hT : MemLp (FourPapersCommon.continuousAdaptedTimeCut (fun s ω => g (X s ω)) T)
      2 (nonnegativeLebesgueMeasure.prod P))
    (htmem : MemLp (FourPapersCommon.continuousAdaptedTimeCut (fun s ω => g (X s ω)) t)
      2 (nonnegativeLebesgueMeasure.prod P)) :
    FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t
      (coefficientPredictableActual hXa hXc hg T hT) = coefficientPredictableActual hXa hXc hg t htmem := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn F t
    (coefficientPredictableActual hXa hXc hg T hT), hT.coeFn_toLp, htmem.coeFn_toLp]
    with q hcut hTcoe htcoe
  change (coefficientPredictableActual hXa hXc hg T hT : ℝ≥0 × Ω → ℝ) q = _ at hTcoe
  change (coefficientPredictableActual hXa hXc hg t htmem : ℝ≥0 × Ω → ℝ) q = _ at htcoe
  rw [hcut]
  unfold FourPapersCommon.FilteredBrownian.predictableTimeFrame
  by_cases hq : q.1 ∈ Ioc (0 : ℝ≥0) t
  · rw [indicator_of_mem (show q ∈ Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω) from ⟨hq, mem_univ _⟩)]
    rw [hTcoe, htcoe]
    have hqT : q.1 ∈ Ioc (0 : ℝ≥0) T := ⟨hq.1, hq.2.trans ht⟩
    simp only [FourPapersCommon.continuousAdaptedTimeCut, hq, hqT, ite_true]
  · rw [indicator_of_notMem (show q ∉ Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω) from fun h => hq h.1), htcoe]
    simp only [FourPapersCommon.continuousAdaptedTimeCut, hq, ite_false]

lemma driverItoMap_eq_vectorIto (D : BrownianDriver N P F) (U : Fin N → PredictableProcessL2 F P) :
    driverItoMap D U = vectorIto D U := by
  rw [driverItoMap_apply]
  rfl

@[expose] def cutDrift (b : Fin N → State N → ℝ) (X : ℝ≥0 → Ω → State N) (T : ℝ≥0) :
    Fin N → ℝ≥0 → Ω → ℝ :=
  fun k s ω => FourPapersCommon.continuousAdaptedTimeCut (fun r η => b k (X r η)) T (s, ω)

lemma integratedDrift_cutDrift (b : Fin N → State N → ℝ)
    (X : ℝ≥0 → Ω → State N) (T t : ℝ≥0) (ht : t ≤ T) (k : Fin N) (ω : Ω) :
    integratedDrift (cutDrift b X T k) t ω =
      ∫ s in (0 : ℝ)..(t : ℝ), b k (X s.toNNReal ω) := by
  rw [← driftPrimitive_eq_integratedDrift]
  rw [← PredictableDriftTime.primitive_eq_real_intervalIntegral (fun q : ℝ≥0 × Unit => b k (X q.1 ω)) t ()]
  unfold driftPrimitive PredictableDriftTime.primitive
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  have hsT : s ∈ Ioc (0 : ℝ≥0) T := ⟨hs.1, hs.2.trans ht⟩
  simp only [cutDrift, FourPapersCommon.continuousAdaptedTimeCut, hsT, ite_true]

omit [MeasurableSpace Ω] in
lemma cutDrift_integrable (b : Fin N → State N → ℝ) (hb : ∀ k, Continuous (b k))
    (X : ℝ≥0 → Ω → State N) (hXc : ∀ ω, Continuous (fun s => X s ω))
    (T : ℝ≥0) (k : Fin N) (ω : Ω) :
    IntegrableOn (fun s => cutDrift b X T k s ω) (Ioc 0 T) nonnegativeLebesgueMeasure := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
    ((hb k).comp (hXc ω)).continuousOn
  have hsm : StronglyMeasurable (fun s => cutDrift b X T k s ω) := by
    unfold cutDrift FourPapersCommon.continuousAdaptedTimeCut
    exact StronglyMeasurable.ite measurableSet_Ioc ((hb k).comp (hXc ω)).stronglyMeasurable stronglyMeasurable_const
  change Integrable _ (FourPapersCommon.FilteredBrownian.finiteTimeMeasure T)
  apply memLp_one_iff_integrable.mp
  apply MemLp.of_bound hsm.aestronglyMeasurable (max C 0)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  simp only [cutDrift, FourPapersCommon.continuousAdaptedTimeCut, hs, ite_true]
  exact (hC s ⟨hs.1.le, hs.2⟩).trans (le_max_left _ _)

omit [MeasurableSpace Ω] in
lemma stopped_cutDrift_eq (b : Fin N → State N → ℝ) (X : ℝ≥0 → Ω → State N)
    (τ : Ω → ℝ≥0) (T : ℝ≥0) (k : Fin N) (s : ℝ≥0) (ω : Ω) :
    stoppedDrift (cutDrift b X T k) τ s ω = stoppedTimeCoefficient τ T (s, ω) * b k (X s ω) := by
  unfold stoppedDrift cutDrift FourPapersCommon.continuousAdaptedTimeCut stoppedTimeCoefficient
  by_cases hs : s ∈ Ioc (0 : ℝ≥0) T <;> by_cases hτ : s ≤ τ ω <;> simp [hs, hτ]

omit [MeasurableSpace Ω] in
lemma stopped_coefficient_cut (g : State N → ℝ) (X : ℝ≥0 → Ω → State N)
    (τ : Ω → ℝ≥0) (T : ℝ≥0) (q : ℝ≥0 × Ω) :
    stoppedTimeCoefficient τ T q * FourPapersCommon.continuousAdaptedTimeCut (fun s ω => g (X s ω)) T q =
      stoppedTimeCoefficient τ T q * g (X q.1 q.2) := by
  unfold stoppedTimeCoefficient FourPapersCommon.continuousAdaptedTimeCut
  by_cases hs : q.1 ∈ Ioc (0 : ℝ≥0) T <;> by_cases hτ : q.1 ≤ τ q.2 <;> simp [hs, hτ]

omit [MeasurableSpace Ω] in
lemma stopped_physical_drift_cutoff (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0)
    (hR : 0 < (R : ℝ)) (X : ℝ≥0 → Ω → State N) (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hbound : ∀ s ω, ‖stoppedState X τ s ω‖ ≤ R) (k : Fin N) (s : ℝ≥0) (ω : Ω) :
    stoppedTimeCoefficient τ T (s, ω) * CutoffSDE.cutoffDrift β J R hR k (X s ω) =
      stoppedPhysicalDrift β (hamiltonianGradient J) (stoppedState X τ) τ T k s ω := by
  unfold stoppedPhysicalDrift
  by_cases hs : s ∈ Ioc (0 : ℝ≥0) T ∧ s ≤ τ ω
  · have hY : stoppedState X τ s ω = X s ω := by simp only [stoppedState, min_eq_left hs.2]
    rw [hY]
    rw [CutoffSDE.cutoffDrift_eq β J R hR _ (hY ▸ hbound s ω)]
    rfl
  · simp only [stoppedTimeCoefficient, hs, ite_false, zero_mul]

omit [MeasurableSpace Ω] in
lemma stopped_physical_noise_cutoff (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (X : ℝ≥0 → Ω → State N) (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hbound : ∀ s ω, ‖stoppedState X τ s ω‖ ≤ R) (k i : Fin N) (q : ℝ≥0 × Ω) :
    stoppedTimeCoefficient τ T q * CutoffSDE.cutoffNoise N R hR k i (X q.1 q.2) =
      stoppedTimeCoefficient τ T q * noiseColumn (stoppedState X τ q.1 q.2) i k := by
  by_cases hs : q.1 ∈ Ioc (0 : ℝ≥0) T ∧ q.1 ≤ τ q.2
  · have hY : stoppedState X τ q.1 q.2 = X q.1 q.2 := by simp only [stoppedState, min_eq_left hs.2]
    rw [hY, CutoffSDE.cutoffNoise_eq N R hR _ (hY ▸ hbound q.1 q.2)]
  · simp only [stoppedTimeCoefficient, hs, ite_false, zero_mul]

/-- The actual all-path continuous cutoff solution starting on the sphere
never leaves it before its horizon. The cutoff radius strictly contains
the sphere; no sphere hypothesis on the evolving state is used. -/
theorem onSphere_of_cutoff_solution (hN : N ≠ 0) (D : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (x0 : State N) (hx0 : OnSphere x0)
    (X : ℝ≥0 → Ω → State N) (hXc : ∀ ω, Continuous (fun s => X s ω))
    (T : ℝ≥0) (hsigma : ∀ i j, Continuous (CutoffSDE.cutoffNoise N R hR i j))
    (hsol : IsLocalStrongSolutionOn (CutoffSDE.cutoffDrift β J R hR) (CutoffSDE.cutoffNoise N R hR)
      hsigma D x0 X T) (hX0 : ∀ ω, X 0 ω = x0) :
    ∀ᵐ ω ∂P, ∀ t, t ≤ T → OnSphere (X t ω) := by
  rcases hsol with ⟨hXa, hXcae, hbmem, hsigmamem, heq⟩
  let b := CutoffSDE.cutoffDrift β J R hR
  have hb : ∀ k, Continuous (b k) := by
    obtain ⟨K, hK⟩ := CutoffSDE.cutoffDrift_lipschitz β J R hR
    exact fun k => (hK k).continuous
  let τ := radiusHit X T R
  have hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)) := isStoppingTime_radiusHit X hXa hXc T R
  have hτbound : ∀ ω, τ ω ≤ T := radiusHit_le X hXc T R
  let Y := stoppedState X τ
  have hYa : StronglyAdapted F Y := stoppedState_stronglyAdapted X hXa hXc hτ
  have hYc : ∀ ω, Continuous (fun s => Y s ω) := stoppedState_continuous X hXc τ
  have hinitialBound : ∀ ω, ‖X 0 ω‖ ≤ R := by
    intro ω
    rw [hX0 ω]
    have hsq := (onSphere_iff_norm_sq x0).mp hx0
    nlinarith [norm_nonneg x0, R.coe_nonneg]
  have hYbound : ∀ s ω, ‖Y s ω‖ ≤ R := stoppedState_radius_bound X hXc T R hinitialBound
  let A0 (k : Fin N) := coefficientPredictableActual hXa hXcae (hb k) T (hbmem k)
  let U0 (k i : Fin N) := coefficientPredictableActual hXa hXcae (hsigma k i) T (hsigmamem k i T le_rfl)
  let A (k : Fin N) := stoppedIntegrand hτ T (A0 k)
  let U (k i : Fin N) := stoppedIntegrand hτ T (U0 k i)
  have hA : ∀ k, (A k : ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun q => stoppedPhysicalDrift β (hamiltonianGradient J) Y τ T k q.1 q.2 := by
    intro k
    filter_upwards [stoppedIntegrand_coe hτ T (A0 k), (hbmem k).coeFn_toLp] with q hstop hcoef
    change (A0 k : ℝ≥0 × Ω → ℝ) q = _ at hcoef
    rw [hstop, hcoef, stopped_coefficient_cut]
    exact stopped_physical_drift_cutoff β J R hR X τ T hYbound k q.1 q.2
  have hU : ∀ k i, (U k i : ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun q => stoppedTimeCoefficient τ T q * noiseColumn (Y q.1 q.2) i k := by
    intro k i
    filter_upwards [stoppedIntegrand_coe hτ T (U0 k i), (hsigmamem k i T le_rfl).coeFn_toLp] with q hstop hcoef
    change (U0 k i : ℝ≥0 × Ω → ℝ) q = _ at hcoef
    rw [hstop, hcoef, stopped_coefficient_cut]
    exact stopped_physical_noise_cutoff R hR X τ T hYbound k i q
  have hY0 : ∀ᵐ ω ∂P, OnSphere (Y 0 ω) := .of_forall (fun ω => by
    simpa only [Y, stoppedState, min_eq_left (zero_le : (0 : ℝ≥0) ≤ τ ω), hX0 ω] using hx0)
  have hdecomp : ∀ k s, coordinates Y k s =ᵐ[P] fun ω => coordinates Y k 0 ω +
      integratedDrift (stoppedPhysicalDrift β (hamiltonianGradient J) Y τ T k) s ω + vectorProcess D (U k) s ω := by
    intro k s
    obtain ⟨M, hM⟩ := exists_continuousModification_vectorProcess D (U0 k)
    have hfixed : ∀ t, t ≤ T → (fun ω => X t ω k) =ᵐ[P] fun ω => X 0 ω k +
        integratedDrift (cutDrift b X T k) t ω + M t ω := by
      intro t ht
      have hnoise : driverItoMap D (fun i => coefficientPredictableActual hXa hXcae (hsigma k i) t
          (hsigmamem k i t ht)) = vectorProcessLp D (U0 k) t := by
        rw [driverItoMap_eq_vectorIto]
        unfold vectorProcessLp
        congr 1
        funext i
        exact (coefficientPredictableActual_timeRestrict hXa hXcae (hsigma k i) T t ht _ _).symm
      have hi := (vectorProcessLp_ae_eq D (U0 k) t).trans (hM.fixedTime_ae_eq t)
      have htEq := heq t ht k
      rw [hnoise] at htEq
      filter_upwards [htEq, hi] with ω hω hi
      rw [hX0 ω, integratedDrift_cutDrift b X T t ht k ω]
      simpa only [b, hi] using hω
    have hstop := stopped_equation D hτ T hτbound (U0 k) (fun t ω => X t ω k)
      (cutDrift b X T k) M (fun ω => (CutoffSDE.coordinate_lipschitz k).continuous.comp (hXc ω))
      (cutDrift_integrable b hb X hXc T k) hM.fixedTime_ae_eq hM.continuous_paths hfixed s
    filter_upwards [hstop] with ω hω
    simp only [coordinates, Y, stoppedState, zero_min]
    rw [hω]
    congr 1
    congr 1
    apply congrArg (fun f => integratedDrift f s ω)
    funext r η
    rw [stopped_cutDrift_eq]
    exact stopped_physical_drift_cutoff β J R hR X τ T hYbound k r η
  have hYsphere := bounded_stopped_physical_solution_onSphere hN D β (hamiltonianGradient J)
    (hamiltonianGradient_contDiff J).continuous Y hYa hYc R hR hYbound τ hτ T A U hA hU hY0 hdecomp
  filter_upwards [hYsphere] with ω hω
  have hτeq : τ ω = T := by
    apply le_antisymm (hτbound ω)
    by_contra h
    have hτlt : τ ω < T := lt_of_not_ge h
    have hr := radius_eq_at_hit X hXc T R hinitialBound ω hτlt
    have hYhit := (onSphere_iff_norm_sq (Y (τ ω) ω)).mp (hω (τ ω) (hτbound ω))
    simp only [Y, stoppedState, min_self] at hYhit
    rw [hr] at hYhit
    linarith
  intro t ht
  have hs := hω t ht
  simpa only [Y, stoppedState, hτeq, min_eq_left ht] using hs

@[expose] def initialNormalized (X : ℝ≥0 → Ω → State N) (x0 : State N) : ℝ≥0 → Ω → State N :=
  fun s ω => if X 0 ω = x0 then X s ω else x0

lemma initialNormalized_adapted (X : ℝ≥0 → Ω → State N) (x0 : State N)
    (hXa : StronglyAdapted F X) : StronglyAdapted F (initialNormalized X x0) := by
  intro s
  have hevent : MeasurableSet[F 0] {ω | X 0 ω = x0} :=
    measurableSet_eq_fun (hXa 0).measurable measurable_const
  exact StronglyMeasurable.ite ((F.mono (zero_le : (0 : ℝ≥0) ≤ s)) _ hevent)
    (hXa s) stronglyMeasurable_const

omit [MeasurableSpace Ω] in
lemma initialNormalized_continuous (X : ℝ≥0 → Ω → State N) (x0 : State N)
    (hXc : ∀ ω, Continuous (fun s => X s ω)) :
    ∀ ω, Continuous (fun s => initialNormalized X x0 s ω) := by
  intro ω
  by_cases h : X 0 ω = x0
  · simpa only [initialNormalized, h, ite_true] using hXc ω
  · simpa only [initialNormalized, h, ite_false] using (continuous_const : Continuous (fun _ : ℝ≥0 => x0))

omit [MeasurableSpace Ω] in
lemma initialNormalized_initial (X : ℝ≥0 → Ω → State N) (x0 : State N) :
    ∀ ω, initialNormalized X x0 0 ω = x0 := by
  intro ω
  unfold initialNormalized
  split_ifs with h
  · exact h
  · rfl

omit [IsProbabilityMeasure P] in
lemma initialNormalized_ae (X : ℝ≥0 → Ω → State N) (x0 : State N)
    (hX0 : ∀ᵐ ω ∂P, X 0 ω = x0) : ∀ᵐ ω ∂P, ∀ s, initialNormalized X x0 s ω = X s ω := by
  filter_upwards [hX0] with ω hω
  intro s
  simp only [initialNormalized, hω, ite_true]

/-- The null initial-path normalization is constructed within the actual
filtration at time zero. Consequently no all-path initial assumption is
needed for sphere preservation of the actual cutoff strong solution. -/
theorem onSphere_of_cutoff_solution_aeInitial (hN : N ≠ 0) (D : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (x0 : State N) (hx0 : OnSphere x0)
    (X : ℝ≥0 → Ω → State N) (hXc : ∀ ω, Continuous (fun s => X s ω))
    (T : ℝ≥0) (hsigma : ∀ i j, Continuous (CutoffSDE.cutoffNoise N R hR i j))
    (hsol : IsLocalStrongSolutionOn (CutoffSDE.cutoffDrift β J R hR) (CutoffSDE.cutoffNoise N R hR)
      hsigma D x0 X T) :
    ∀ᵐ ω ∂P, ∀ t, t ≤ T → OnSphere (X t ω) := by
  have hXinit := hsol.initial
  have hsolCopy := hsol
  obtain ⟨hXa, hXcae, hb, hsig, heq⟩ := hsol
  let Y := initialNormalized X x0
  have hYa := initialNormalized_adapted X x0 hXa
  have hYc := initialNormalized_continuous X x0 hXc
  have hYX := initialNormalized_ae X x0 hXinit
  have hYsol := AllPathSDE.IsLocalStrongSolutionOn.path_congr hsolCopy hYa (.of_forall hYc) hYX
  have hYsphere := onSphere_of_cutoff_solution hN D β J R hR hNR x0 hx0 Y hYc T hsigma hYsol
    (initialNormalized_initial X x0)
  filter_upwards [hYsphere, hYX] with ω hω hYXω
  intro t ht
  have hs := hω t ht
  change OnSphere (initialNormalized X x0 t ω) at hs
  simpa only [hYXω t] using hs

lemma continuousAdaptedTimeCut_coefficient_congr {X : ℝ≥0 → Ω → State N}
    {g h : State N → ℝ} {T t : ℝ≥0} (ht : t ≤ T)
    (heq : ∀ᵐ ω ∂P, ∀ s, s ≤ T → g (X s ω) = h (X s ω)) :
    FourPapersCommon.continuousAdaptedTimeCut (fun s ω => g (X s ω)) t
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        FourPapersCommon.continuousAdaptedTimeCut (fun s ω => h (X s ω)) t := by
  have hcommon := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae heq
  filter_upwards [hcommon] with q hq
  by_cases hs : q.1 ∈ Ioc (0 : ℝ≥0) t
  · simp only [FourPapersCommon.continuousAdaptedTimeCut, hs, ite_true]
    exact hq q.1 (hs.2.trans ht)
  · simp only [FourPapersCommon.continuousAdaptedTimeCut, hs, ite_false]

/-- Changing actual coefficients along an almost-sure common path event
preserves both their genuine predictable L² classes and the SDE equation. -/
theorem coefficient_congr_onPath {b b' : Fin N → State N → ℝ}
    {sigma sigma' : Fin N → Fin N → State N → ℝ}
    {hsigma : ∀ i j, Continuous (sigma i j)} (hsigma' : ∀ i j, Continuous (sigma' i j))
    {D : BrownianDriver N P F} {x0 : State N} {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (hsol : IsLocalStrongSolutionOn b sigma hsigma D x0 X T)
    (hbEq : ∀ i, ∀ᵐ ω ∂P, ∀ s, s ≤ T → b' i (X s ω) = b i (X s ω))
    (hSEq : ∀ i j, ∀ᵐ ω ∂P, ∀ s, s ≤ T → sigma' i j (X s ω) = sigma i j (X s ω)) :
    IsLocalStrongSolutionOn b' sigma' hsigma' D x0 X T := by
  obtain ⟨hXa, hXc, hbmem, hSmem, heq⟩ := hsol
  have hbmem' := fun i => (hbmem i).ae_eq
    (continuousAdaptedTimeCut_coefficient_congr le_rfl (hbEq i)).symm
  have hSmem' : ∀ i j (t : ℝ≥0), t ≤ T → MemLp
      (FourPapersCommon.continuousAdaptedTimeCut (fun s ω => sigma' i j (X s ω)) t)
      2 (nonnegativeLebesgueMeasure.prod P) := fun i j t ht =>
    (hSmem i j t ht).ae_eq (continuousAdaptedTimeCut_coefficient_congr ht (hSEq i j)).symm
  refine ⟨hXa, hXc, hbmem', hSmem', ?_⟩
  intro t ht i
  have hclasses : (fun j => coefficientPredictableActual hXa hXc (hsigma' i j) t (hSmem' i j t ht)) =
      (fun j => coefficientPredictableActual hXa hXc (hsigma i j) t (hSmem i j t ht)) := by
    funext j
    apply Subtype.ext
    apply Lp.ext
    exact (hSmem' i j t ht).coeFn_toLp.trans
      ((continuousAdaptedTimeCut_coefficient_congr ht (hSEq i j)).trans (hSmem i j t ht).coeFn_toLp.symm)
  rw [hclasses]
  filter_upwards [heq t ht i, hbEq i] with ω hω hbω
  have hdrift : (∫ s in (0 : ℝ)..(t : ℝ), b' i (X s.toNNReal ω)) =
      ∫ s in (0 : ℝ)..(t : ℝ), b i (X s.toNNReal ω) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hsT : s.toNNReal ≤ T := by
      have hst : s ≤ (t : ℝ) := (uIcc_of_le t.coe_nonneg ▸ hs).2
      exact (Real.toNNReal_le_toNNReal hst).trans (by simpa only [Real.toNNReal_coe] using ht)
    exact hbω _ hsT
  rw [hdrift]
  exact hω

lemma physical_noise_continuous (i j : Fin N) : Continuous (fun x : State N => noiseColumn x j i) :=
  (CutoffSDE.coordinate_lipschitz i).continuous.comp (contDiff_noiseColumn j).continuous

/-- Sphere invariance removes the cutoff in the actual coefficient classes
and the actual matrix SDE equation, simultaneously throughout its horizon. -/
theorem physical_solution_of_cutoff (hN : N ≠ 0) (D : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (x0 : State N) (hx0 : OnSphere x0)
    (X : ℝ≥0 → Ω → State N) (hXc : ∀ ω, Continuous (fun s => X s ω))
    (T : ℝ≥0) (hsigma : ∀ i j, Continuous (CutoffSDE.cutoffNoise N R hR i j))
    (hsol : IsLocalStrongSolutionOn (CutoffSDE.cutoffDrift β J R hR) (CutoffSDE.cutoffNoise N R hR)
      hsigma D x0 X T) :
    IsLocalStrongSolutionOn (fun i x => hamiltonianDrift β J x i) (fun i j x => noiseColumn x j i)
      physical_noise_continuous D x0 X T ∧ (∀ᵐ ω ∂P, ∀ t, t ≤ T → OnSphere (X t ω)) := by
  have hSphere := onSphere_of_cutoff_solution_aeInitial hN D β J R hR hNR x0 hx0 X hXc T hsigma hsol
  have hbound : ∀ᵐ ω ∂P, ∀ t, t ≤ T → ‖X t ω‖ ≤ R := by
    filter_upwards [hSphere] with ω hω
    intro t ht
    have hsq := (onSphere_iff_norm_sq (X t ω)).mp (hω t ht)
    nlinarith [norm_nonneg (X t ω), R.coe_nonneg]
  refine ⟨coefficient_congr_onPath physical_noise_continuous hsol ?_ ?_, hSphere⟩
  · intro i
    filter_upwards [hbound] with ω hω
    intro t ht
    exact (CutoffSDE.cutoffDrift_eq β J R hR _ (hω t ht) i).symm
  · intro i j
    filter_upwards [hbound] with ω hω
    intro t ht
    exact (CutoffSDE.cutoffNoise_eq N R hR _ (hω t ht) i j).symm

/-- Genuine local existence for the untruncated finite-N hard-sphere
Hamiltonian SDE, on a constructed null augmentation preserving the full
independent Brownian driver. Its sphere property is proved from the SDE. -/
theorem exists_local_physical_hamiltonian_strongSolution (hN : N ≠ 0)
    (D : BrownianDriver N P F) (β : ℝ) (J : FiniteModel.Disorder N p)
    (x0 : State N) (hx0 : OnSphere x0) :
    ∃ T : ℝ≥0, 0 < T ∧ ∃ X : ℝ≥0 → Ω → State N,
      (∀ ω, Continuous (fun t => X t ω)) ∧
      IsLocalStrongSolutionOn (fun i x => hamiltonianDrift β J x i) (fun i j x => noiseColumn x j i)
        physical_noise_continuous (NullAugmentation.driver D) x0 X T ∧
      (∀ᵐ ω ∂P, ∀ t, t ≤ T → OnSphere (X t ω)) := by
  let R : ℝ≥0 := N + 1
  have hR : 0 < (R : ℝ) := by simp only [R, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]; positivity
  have hNR : (N : ℝ) < (R : ℝ)^2 := by
    simp only [R, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
    nlinarith [sq_nonneg (N : ℝ), Nat.cast_nonneg (α := ℝ) N]
  obtain ⟨T, hT, X, hXc, hsigma, hsol⟩ := AllPathSDE.exists_allPath_cutoff_hamiltonian_strongSolution D β J R hR x0
  have hphysical := physical_solution_of_cutoff hN (NullAugmentation.driver D) β J R hR hNR x0 hx0 X hXc T hsigma hsol
  exact ⟨T, hT, X, hXc, hphysical⟩

end SphericalAging.CutoffSphere
