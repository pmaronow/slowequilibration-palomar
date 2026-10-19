module

public import SphericalAging.RandomInitialSDE
public import SphericalAging.CutoffSphere
public import SphericalAging.SphereInitialLaw

public section

/-! Genuine sphere preservation and global physical Hamiltonian dynamics
with an F₀-measurable L² random initial state. The stopped radial equation
is derived from the actual matrix SDE, and the cutoff is proved inactive. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.RandomInitialSphere
open HardSphereDynamics LocalSDE RandomInitialSDE VectorIto SpherePreservation StoppedVectorIto
open ClosedHitStopping StoppedSDE RadialItoRepresentation WeightedDriftSums CutoffSphere
set_option maxHeartbeats 2200000
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem IsStrongSolutionOn.initial {b : Fin N → State N → ℝ}
    {sigma : Fin N → Fin N → State N → ℝ} {hsigma : ∀ i j, Continuous (sigma i j)}
    {D : BrownianDriver N P F} {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (h : IsStrongSolutionOn b sigma hsigma D Z0 X T) :
    ∀ᵐ omega ∂P, X 0 omega = Z0 omega := by
  rcases h with ⟨hXa, hXc, hbmem, hsigmamem, heq⟩
  have hi : ∀ i : Fin N, ∀ᵐ omega ∂P, (X 0 omega) i = Z0 omega i := by
    intro i
    have hzero : (fun j => coefficientPredictableActual hXa hXc (hsigma i j) 0
        (hsigmamem i j 0 (zero_le : 0 ≤ T))) = (0 : Fin N → PredictableProcessL2 F P) := by
      funext j
      exact coefficientPredictableActual_zero hXa hXc (hsigma i j) _
    have h0 := heq 0 (zero_le : 0 ≤ T) i
    rw [hzero, map_zero] at h0
    filter_upwards [h0, Lp.coeFn_zero ℝ 2 P] with omega homega hz
    simpa only [NNReal.coe_zero, intervalIntegral.integral_same, add_zero, hz, Pi.zero_apply] using homega
  filter_upwards [ae_all_iff.mpr hi] with omega homega
  exact PiLp.ext homega


theorem IsStrongSolutionOn.path_congr {b : Fin N → State N → ℝ}
    {sigma : Fin N → Fin N → State N → ℝ} {hsigma : ∀ i j, Continuous (sigma i j)}
    {D : BrownianDriver N P F} {Z0 : Ω → State N} {X Y : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (hX : IsStrongSolutionOn b sigma hsigma D Z0 X T)
    (hYa : StronglyAdapted F Y) (hYc : ∀ᵐ omega ∂P, Continuous (fun s => Y s omega))
    (hYX : ∀ᵐ omega ∂P, ∀ t, Y t omega = X t omega) :
    IsStrongSolutionOn b sigma hsigma D Z0 Y T := by
  rcases hX with ⟨hXa, hXc, hbX, hsigmaX, hXeq⟩
  have hbY : ∀ i, MemLp (FourPapersCommon.continuousAdaptedTimeCut
      (fun s omega => b i (Y s omega)) T) 2 (nonnegativeLebesgueMeasure.prod P) :=
    fun i => (hbX i).ae_eq (AllPathSDE.timeCut_path_congr hYX (b i) T).symm
  have hsigmaY : ∀ i j (t : ℝ≥0), t ≤ T → MemLp
      (FourPapersCommon.continuousAdaptedTimeCut (fun s omega => sigma i j (Y s omega)) t)
      2 (nonnegativeLebesgueMeasure.prod P) :=
    fun i j t ht => (hsigmaX i j t ht).ae_eq (AllPathSDE.timeCut_path_congr hYX (sigma i j) t).symm
  refine ⟨hYa, hYc, hbY, hsigmaY, ?_⟩
  intro t ht i
  have hnoise : driverItoMap D (fun j => coefficientPredictableActual hYa hYc (hsigma i j) t
      (hsigmaY i j t ht)) = driverItoMap D (fun j => coefficientPredictableActual hXa hXc (hsigma i j) t
        (hsigmaX i j t ht)) := by
    congr 1
    funext j
    exact AllPathSDE.coefficientPredictableActual_congr hXa hXc hYa hYc hYX (hsigma i j) t _ _
  rw [hnoise]
  filter_upwards [hYX, hXeq t ht i] with omega hYXomega hXomega
  rw [hYXomega t]
  have hdrift : (∫ s in (0 : ℝ)..(t : ℝ), b i (Y s.toNNReal omega)) =
      ∫ s in (0 : ℝ)..(t : ℝ), b i (X s.toNNReal omega) := by
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [hYXomega s.toNNReal]
  rw [hdrift]
  exact hXomega


theorem onSphere_of_cutoff_solution (hN : N ≠ 0) (D : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (Z0 : Ω → State N)
    (X : ℝ≥0 → Ω → State N) (hXc : ∀ ω, Continuous (fun s => X s ω))
    (T : ℝ≥0) (hsigma : ∀ i j, Continuous (CutoffSDE.cutoffNoise N R hR i j))
    (hsol : IsStrongSolutionOn (CutoffSDE.cutoffDrift β J R hR) (CutoffSDE.cutoffNoise N R hR)
      hsigma D Z0 X T) (hinitial : ∀ ω, OnSphere (X 0 ω)) (hX0 : ∀ᵐ ω ∂P, X 0 ω = Z0 ω) :
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
    have hsq := (onSphere_iff_norm_sq (X 0 ω)).mp (hinitial ω)
    nlinarith [norm_nonneg (X 0 ω), R.coe_nonneg]
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
    simpa only [Y, stoppedState, min_eq_left (zero_le : (0 : ℝ≥0) ≤ τ ω)] using hinitial ω)
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
      filter_upwards [htEq, hi, hX0] with ω hω hi hX0ω
      rw [hX0ω, integratedDrift_cutDrift b X T t ht k ω]
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


/-- Normalize only exceptional initial paths using an actual F₀ event. -/
@[expose] def initialSphereNormalized (X : ℝ≥0 → Ω → State N) (xref : State N) : ℝ≥0 → Ω → State N :=
  by
  classical
  exact fun t omega => if OnSphere (X 0 omega) then X t omega else xref

theorem initialSphereNormalized_adapted (X : ℝ≥0 → Ω → State N) (xref : State N)
    (hXa : StronglyAdapted F X) : StronglyAdapted F (initialSphereNormalized X xref) := by
  classical
  have hn : StronglyMeasurable[F 0] (fun omega => ‖X 0 omega‖^2) :=
    (continuous_norm.pow 2).comp_stronglyMeasurable (hXa 0)
  have hc : StronglyMeasurable[F 0] (fun _ : Ω => (N : ℝ)) := stronglyMeasurable_const
  have hevent : MeasurableSet[F 0] {omega | OnSphere (X 0 omega)} := by
    simpa only [onSphere_iff_norm_sq] using StronglyMeasurable.measurableSet_eq_fun hn hc
  intro t
  exact StronglyMeasurable.ite ((F.mono (zero_le : (0 : ℝ≥0) ≤ t)) _ hevent)
    (hXa t) stronglyMeasurable_const

omit [MeasurableSpace Ω] in
theorem initialSphereNormalized_continuous (X : ℝ≥0 → Ω → State N) (xref : State N)
    (hXc : ∀ omega, Continuous (fun t => X t omega)) :
    ∀ omega, Continuous (fun t => initialSphereNormalized X xref t omega) := by
  intro omega
  by_cases h : OnSphere (X 0 omega)
  · simpa only [initialSphereNormalized,h,ite_true] using hXc omega
  · simpa only [initialSphereNormalized,h,ite_false] using (continuous_const : Continuous (fun _ : ℝ≥0 => xref))

omit [MeasurableSpace Ω] in
theorem initialSphereNormalized_initial (X : ℝ≥0 → Ω → State N) (xref : State N)
    (hxref : OnSphere xref) : ∀ omega, OnSphere (initialSphereNormalized X xref 0 omega) := by
  intro omega
  by_cases h : OnSphere (X 0 omega)
  · simp only [initialSphereNormalized,h,ite_true]
  · simpa only [initialSphereNormalized,h,ite_false] using hxref

/-- A probability-one spherical random initial state suffices; the exceptional
initial paths are normalized inside the actual filtration. -/
theorem onSphere_of_cutoff_solution_aeInitial (hN : N ≠ 0) (D : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (Z0 : Ω → State N) (hZsphere : ∀ᵐ omega ∂P, OnSphere (Z0 omega))
    (X : ℝ≥0 → Ω → State N) (hXc : ∀ omega, Continuous (fun t => X t omega))
    (T : ℝ≥0) (hsigma : ∀ i j, Continuous (CutoffSDE.cutoffNoise N R hR i j))
    (hsol : IsStrongSolutionOn (CutoffSDE.cutoffDrift β J R hR) (CutoffSDE.cutoffNoise N R hR)
      hsigma D Z0 X T) : ∀ᵐ omega ∂P, ∀ t, t ≤ T → OnSphere (X t omega) := by
  have hXinit := IsStrongSolutionOn.initial hsol
  obtain ⟨omega0,homega0⟩ := hZsphere.exists
  let xref := Z0 omega0
  let Y := initialSphereNormalized X xref
  have hYa := initialSphereNormalized_adapted X xref hsol.choose
  have hYc := initialSphereNormalized_continuous X xref hXc
  have hYX : ∀ᵐ omega ∂P, ∀ t, Y t omega = X t omega := by
    filter_upwards [hZsphere,hXinit] with omega hsp hini
    have hx : OnSphere (X 0 omega) := hini.symm ▸ hsp
    intro t
    simp only [Y,initialSphereNormalized,hx,ite_true]
  have hYsol := IsStrongSolutionOn.path_congr hsol hYa (.of_forall hYc) hYX
  have hYsphere := onSphere_of_cutoff_solution hN D β J R hR hNR Z0 Y hYc T hsigma hYsol
    (initialSphereNormalized_initial X xref homega0) (IsStrongSolutionOn.initial hYsol)
  filter_upwards [hYsphere,hYX] with omega hsp heq
  intro t ht
  simpa only [heq t] using hsp t ht

theorem coefficient_congr_onPath {b b' : Fin N → State N → ℝ}
    {sigma sigma' : Fin N → Fin N → State N → ℝ}
    {hsigma : ∀ i j, Continuous (sigma i j)} (hsigma' : ∀ i j, Continuous (sigma' i j))
    {D : BrownianDriver N P F} {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (hsol : IsStrongSolutionOn b sigma hsigma D Z0 X T)
    (hbEq : ∀ i, ∀ᵐ ω ∂P, ∀ s, s ≤ T → b' i (X s ω) = b i (X s ω))
    (hSEq : ∀ i j, ∀ᵐ ω ∂P, ∀ s, s ≤ T → sigma' i j (X s ω) = sigma i j (X s ω)) :
    IsStrongSolutionOn b' sigma' hsigma' D Z0 X T := by
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

theorem physical_solution_of_cutoff (hN : N ≠ 0) (D : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (Z0 : Ω → State N) (hZsphere : ∀ᵐ omega ∂P, OnSphere (Z0 omega))
    (X : ℝ≥0 → Ω → State N) (hXc : ∀ ω, Continuous (fun s => X s ω))
    (T : ℝ≥0) (hsigma : ∀ i j, Continuous (CutoffSDE.cutoffNoise N R hR i j))
    (hsol : IsStrongSolutionOn (CutoffSDE.cutoffDrift β J R hR) (CutoffSDE.cutoffNoise N R hR)
      hsigma D Z0 X T) :
    IsStrongSolutionOn (fun i x => hamiltonianDrift β J x i) (fun i j x => noiseColumn x j i)
      physical_noise_continuous D Z0 X T ∧ (∀ᵐ ω ∂P, ∀ t, t ≤ T → OnSphere (X t ω)) := by
  have hSphere := onSphere_of_cutoff_solution_aeInitial hN D β J R hR hNR Z0 hZsphere X hXc T hsigma hsol
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


theorem exists_allPath_global_strongSolution (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) : ∃ X : ℝ≥0 → Ω → State N,
      (∀ omega, Continuous (fun t => X t omega)) ∧
      ∀ T : ℝ≥0, IsStrongSolutionOn b sigma (fun i j => (hsigma i j).continuous)
        (NullAugmentation.driver D) Z0 X T := by
  obtain ⟨X,hXa,hXc,hXsol⟩ := RandomInitialSDE.exists_global_strongSolution (NullAugmentation.driver D) hb hsigma Z0
    (hZ0.mono (NullAugmentation.le_augment F 0)) hmem
  obtain ⟨Y,hYa,hYc,hYX⟩ := NullAugmentation.exists_allPath_continuous_modification_augmented F X hXa hXc
  refine ⟨Y,hYc,fun T => ?_⟩
  exact IsStrongSolutionOn.path_congr (hXsol T) hYa (.of_forall hYc) hYX

theorem exists_allPath_global_cutoff_hamiltonian_strongSolution (D : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ) (hR : 0 < R) (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) :
    ∃ X : ℝ≥0 → Ω → State N, (∀ omega, Continuous (fun t => X t omega)) ∧
      ∃ hsigma : ∀ i j, Continuous (CutoffSDE.cutoffNoise N R hR i j),
        ∀ T : ℝ≥0, IsStrongSolutionOn (CutoffSDE.cutoffDrift β J R hR) (CutoffSDE.cutoffNoise N R hR)
          hsigma (NullAugmentation.driver D) Z0 X T := by
  obtain ⟨Kb,hb⟩ := CutoffSDE.cutoffDrift_lipschitz β J R hR
  obtain ⟨Ks,hsigma⟩ := CutoffSDE.cutoffNoise_lipschitz N R hR
  obtain ⟨X,hXc,hXsol⟩ := exists_allPath_global_strongSolution D hb hsigma Z0 hZ0 hmem
  exact ⟨X,hXc,(fun i j => (hsigma i j).continuous),hXsol⟩

/-- The manuscript's untruncated finite-N hard-sphere Hamiltonian SDE has a
global nonexplosive strongly adapted solution. On one common probability-one
path event it stays on the sphere at every nonnegative time. -/
theorem exists_global_physical_hamiltonian_strongSolution (hN : N ≠ 0)
    (D : BrownianDriver N P F) (β : ℝ) (J : FiniteModel.Disorder N p)
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P)
    (hZsphere : ∀ᵐ omega ∂P, OnSphere (Z0 omega)) :
    ∃ X : ℝ≥0 → Ω → State N, (∀ omega, Continuous (fun t => X t omega)) ∧
      (∀ T : ℝ≥0, IsStrongSolutionOn (fun i x => hamiltonianDrift β J x i)
        (fun i j x => noiseColumn x j i) CutoffSphere.physical_noise_continuous
        (NullAugmentation.driver D) Z0 X T) ∧
      (∀ᵐ omega ∂P, ∀ t, OnSphere (X t omega)) := by
  let R : ℝ≥0 := N+1
  have hR : 0 < (R : ℝ) := by simp only [R,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]; positivity
  have hNR : (N : ℝ) < (R : ℝ)^2 := by
    simp only [R,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]
    nlinarith [sq_nonneg (N : ℝ),Nat.cast_nonneg (α := ℝ) N]
  obtain ⟨X,hXc,hsigma,hXsol⟩ := exists_allPath_global_cutoff_hamiltonian_strongSolution D β J R hR Z0 hZ0 hmem
  have hphysical := fun T => physical_solution_of_cutoff hN (NullAugmentation.driver D)
    β J R hR hNR Z0 hZsphere X hXc T hsigma (hXsol T)
  refine ⟨X,hXc,(fun T => (hphysical T).1),?_⟩
  have hall := ae_all_iff.mpr (fun n : ℕ => (hphysical (GlobalSDE.integerHorizon n)).2)
  filter_upwards [hall] with omega homega
  intro t
  exact homega (Nat.ceil t) t (GlobalSDE.le_integerHorizon_ceil t)


end SphericalAging.RandomInitialSphere
