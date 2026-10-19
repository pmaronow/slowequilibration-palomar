module

public import SphericalAging.GlobalSDE

public section

/-! Actual strong SDE solutions with F₀-measurable square-integrable random
initial states. The initial predictable class is constructed from genuine
elementary integrands; no deterministic-initial or independence premise is
silently substituted for the manuscript's full initial filtration. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.RandomInitialSDE
open HardSphereDynamics PredictableItoTime PredictableDriftTime LocalSDE
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

omit [IsProbabilityMeasure P] in
theorem coordinateInitial_memLp (Z0 : Ω → State N)
    (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) (i : Fin N) :
    MemLp (fun omega => Z0 omega i) 2 P :=
  hmem.norm.mono' (((PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).comp_stronglyMeasurable
    (hZ0.mono (F.le 0))).aestronglyMeasurable) (.of_forall (fun omega => PiLp.norm_apply_le (Z0 omega) i))

@[expose] def coordinateInitialClass (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0)
    (hmem : MemLp Z0 2 P) (i : Fin N) : lpMeas ℝ ℝ (F 0) 2 P :=
  ⟨(coordinateInitial_memLp Z0 hZ0 hmem i).toLp _,
    (((PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).comp_stronglyMeasurable hZ0).aestronglyMeasurable).congr
      (coordinateInitial_memLp Z0 hZ0 hmem i).coeFn_toLp.symm⟩

@[expose] def initialClass (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0)
    (hmem : MemLp Z0 2 P) (T : ℝ≥0) : PredictableStateL2 N F P :=
  ∑ i : Fin N, scalarToStatePredictable i
    (StochasticCalculus.elementaryPredictable F 0 T (coordinateInitialClass Z0 hZ0 hmem i))

theorem initialClass_coeFn (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0)
    (hmem : MemLp Z0 2 P) (T : ℝ≥0) :
    (initialClass Z0 hZ0 hmem T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
      ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun p => Z0 p.2)) := by
  have hs := sumState_coeFn (fun i : Fin N => scalarToStatePredictable i
    (StochasticCalculus.elementaryPredictable F 0 T (coordinateInitialClass Z0 hZ0 hmem i)))
  have hi := ae_all_iff.mpr (fun i : Fin N => scalarToStatePredictable_coeFn i
    (StochasticCalculus.elementaryPredictable F 0 T (coordinateInitialClass Z0 hZ0 hmem i)))
  have hc := ae_all_iff.mpr (fun i : Fin N => StochasticCalculus.elementaryPredictable_coeFn F 0 T
    (coordinateInitialClass Z0 hZ0 hmem i))
  have h0 : ∀ᵐ p ∂nonnegativeLebesgueMeasure.prod P, ∀ i : Fin N,
      (coordinateInitialClass Z0 hZ0 hmem i : RandomL2 P) p.2 = Z0 p.2 i :=
    (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae
      (ae_all_iff.mpr (fun i => (coordinateInitial_memLp Z0 hZ0 hmem i).coeFn_toLp))
  filter_upwards [hs,hi,hc,h0] with p hp hi hc h0
  unfold initialClass
  rw [hp]
  by_cases hpt : p.1 ∈ Ioc 0 T
  · simp only [show p ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨hpt,mem_univ _⟩,
      indicator_of_mem]
    simpa only [hi,hc,hpt,ite_true,h0] using state_sum_basis (Z0 p.2)
  · simp [hi,hc,hpt]

@[expose] def version (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) (T : ℝ≥0) (U : PredictableStateL2 N F P)
    (t : ℝ≥0) (omega : Ω) : State N := Z0 omega + LocalSDE.version D hb hsigma 0 T U t omega

theorem version_stronglyAdapted (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (T : ℝ≥0)
    (U : PredictableStateL2 N F P) : StronglyAdapted F (version D hb hsigma Z0 T U) := fun t =>
  (hZ0.mono (F.mono (zero_le : 0 ≤ t))).add (LocalSDE.version_stronglyAdapted D hb hsigma 0 T U t)

theorem version_continuous (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) (T : ℝ≥0) (U : PredictableStateL2 N F P) :
    ∀ᵐ omega ∂P, Continuous (fun t => version D hb hsigma Z0 T U t omega) :=
  (LocalSDE.version_ae_continuous D hb hsigma 0 T U).mono (fun _ h => continuous_const.add h)

theorem deterministic_initialClass_zero (T : ℝ≥0) :
    LocalSDE.initialClass (N := N) (F := F) (P := P) 0 T = 0 := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [LocalSDE.initialClass_coeFn (F := F) (P := P) (0 : State N) T,
    Lp.coeFn_zero (State N) 2 (nonnegativeLebesgueMeasure.prod P)] with p hp hz
  simpa only [Submodule.coe_zero, hz, indicator_zero, Pi.zero_apply] using hp

theorem version_apply (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) (T : ℝ≥0) (U : PredictableStateL2 N F P) (t : ℝ≥0) (omega : Ω) (i : Fin N) :
    version D hb hsigma Z0 T U t omega i = Z0 omega i +
      driftVersion (predictableCoefficient (hb i) U T) T t omega +
      ∑ j : Fin N, itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j)
        (predictableCoefficient (hsigma i j) U T) t omega := by
  simp only [version, PiLp.add_apply, LocalSDE.version_apply, coordinateVersion, PiLp.zero_apply, zero_add]
  ring

theorem version_timeCut_eq_picard (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P)
    (T : ℝ≥0) (U : PredictableStateL2 N F P) :
    ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun p => version D hb hsigma Z0 T U p.1 p.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
      ((initialClass Z0 hZ0 hmem T + finiteDriftPicardMap hb T U + finiteNoisePicardMap D hsigma T U :
        PredictableStateL2 N F P) : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) := by
  have ho := StrongUniqueness.version_timeCut_eq_picard_ae D hb hsigma (0 : State N) T U
  rw [deterministic_initialClass_zero,zero_add] at ho
  have hi := initialClass_coeFn Z0 hZ0 hmem T
  have ha := Lp.coeFn_add (initialClass Z0 hZ0 hmem T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
    ((finiteDriftPicardMap hb T U + finiteNoisePicardMap D hsigma T U : PredictableStateL2 N F P) :
      Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
  rw [add_assoc]
  filter_upwards [ho,hi,ha] with p hp hi ha
  change _ = ((initialClass Z0 hZ0 hmem T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) +
    ((finiteDriftPicardMap hb T U + finiteNoisePicardMap D hsigma T U : PredictableStateL2 N F P) :
      Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))) p
  rw [ha,Pi.add_apply,hi,← hp]
  by_cases hpt : p ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)
  · simp only [indicator_of_mem hpt,version]
  · simp only [indicator_of_notMem hpt,zero_add]

theorem version_timeCut_eq_fixedPoint (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P)
    (T : ℝ≥0) (U : PredictableStateL2 N F P)
    (hU : U = initialClass Z0 hZ0 hmem T + finiteDriftPicardMap hb T U + finiteNoisePicardMap D hsigma T U) :
    ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun p => version D hb hsigma Z0 T U p.1 p.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) := by
  have hh := version_timeCut_eq_picard D hb hsigma Z0 hZ0 hmem T U
  rw [← hU] at hh
  exact hh

/-- Faithful strong SDE semantics with random initial state; all integrals
use the actual full Brownian filtration. -/
@[expose] def IsStrongSolutionOn (b : Fin N → State N → ℝ) (sigma : Fin N → Fin N → State N → ℝ)
    (hsigma : ∀ i j, Continuous (sigma i j)) (D : BrownianDriver N P F) (Z0 : Ω → State N)
    (X : ℝ≥0 → Ω → State N) (T : ℝ≥0) : Prop :=
  ∃ (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ omega ∂P, Continuous (fun s => X s omega))
    (_hbmem : ∀ i, MemLp (FourPapersCommon.continuousAdaptedTimeCut
      (fun s omega => b i (X s omega)) T) 2 (nonnegativeLebesgueMeasure.prod P))
    (hsigmamem : ∀ i j (t : ℝ≥0), t ≤ T → MemLp
      (FourPapersCommon.continuousAdaptedTimeCut (fun s omega => sigma i j (X s omega)) t) 2
      (nonnegativeLebesgueMeasure.prod P)),
      ∀ (t : ℝ≥0) (ht : t ≤ T), ∀ i : Fin N, ∀ᵐ omega ∂P,
        X t omega i = Z0 omega i + (∫ s in (0 : ℝ)..(t : ℝ), b i (X s.toNNReal omega)) +
          (driverItoMap D (fun j => coefficientPredictableActual hXa hXc (hsigma i j) t
            (hsigmamem i j t ht)) : Ω → ℝ) omega

theorem strongSolution_of_picard_fixedPoint (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P)
    (T : ℝ≥0) (U : PredictableStateL2 N F P)
    (hU : U = initialClass Z0 hZ0 hmem T + finiteDriftPicardMap hb T U + finiteNoisePicardMap D hsigma T U) :
    IsStrongSolutionOn b sigma (fun i j => (hsigma i j).continuous) D Z0 (version D hb hsigma Z0 T U) T := by
  have hXa := version_stronglyAdapted D hb hsigma Z0 hZ0 T U
  have hXc := version_continuous D hb hsigma Z0 T U
  have hXeq := version_timeCut_eq_fixedPoint D hb hsigma Z0 hZ0 hmem T U hU
  refine ⟨hXa,hXc,(fun i => coefficient_timeCut_memLp hXeq (hb i) T le_rfl),
    (fun i j t ht => coefficient_timeCut_memLp hXeq (hsigma i j) t ht),?_⟩
  intro t ht i
  filter_upwards [driftVersion_eq_actual_drift_ae hXeq (hb i),
    actual_driverIto_ae_eq hXeq hXa hXc D (hsigma i) t ht] with omega hdrift hnoise
  rw [version_apply,hnoise]
  simp only [hdrift t ht]

/-- Actual finite-horizon existence with the full original random initial
state. The horizon is arbitrary, and all initial-data regularity is proved
inside the constructed predictable class. -/
theorem exists_strongSolution_on (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) (T : ℝ≥0) :
    ∃ X : ℝ≥0 → Ω → State N, IsStrongSolutionOn b sigma (fun i j => (hsigma i j).continuous) D Z0 X T := by
  obtain ⟨U,hU,_⟩ := GlobalSDE.exists_unique_picard_fixedPoint D hb hsigma T (initialClass Z0 hZ0 hmem T)
  exact ⟨version D hb hsigma Z0 T U,strongSolution_of_picard_fixedPoint D hb hsigma Z0 hZ0 hmem T U hU⟩

section ActualSolution
variable {X : ℝ≥0 → Ω → State N} {U : PredictableStateL2 N F P} {T : ℝ≥0}
  (hXeq : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun p => X p.1 p.2))
    =ᵐ[nonnegativeLebesgueMeasure.prod P] (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
include hXeq

/-- The actual strong integral equation identifies the process with the
continuous Picard version of its own predictable class. -/
theorem strongSolution_eq_version (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) (_hZ0 : StronglyMeasurable[F 0] Z0) (_hmem : MemLp Z0 2 P)
    (hX : IsStrongSolutionOn b sigma (fun i j => (hsigma i j).continuous) D Z0 X T) :
    ∀ᵐ omega ∂P, ∀ t, t ≤ T → X t omega = version D hb hsigma Z0 T U t omega := by
  rcases hX with ⟨hXa, hXc, hbmem, hsigmamem, hactual⟩
  apply StrongUniqueness.continuous_state_processes_ae_eq_of_fixedTime_on hXc (version_continuous D hb hsigma Z0 T U)
  intro t ht
  have hall : ∀ i : Fin N, ∀ᵐ omega ∂P, (X t omega) i = (version D hb hsigma Z0 T U t omega) i := by
    intro i
    filter_upwards [hactual t ht i, driftVersion_eq_actual_drift_ae hXeq (hb i),
      actual_driverIto_ae_eq hXeq hXa hXc D (hsigma i) t ht] with omega heq hdrift hnoise
    rw [version_apply]
    rw [hnoise] at heq
    simpa only [hdrift t ht] using heq
  filter_upwards [ae_all_iff.mpr hall] with omega homega
  exact PiLp.ext (homega)

/-- Every actual strong solution with a genuine predictable state class
satisfies the actual Picard fixed-point equation. -/
theorem strongSolution_fixedPoint (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P)
    (hX : IsStrongSolutionOn b sigma (fun i j => (hsigma i j).continuous) D Z0 X T) :
    U = initialClass Z0 hZ0 hmem T + finiteDriftPicardMap hb T U + finiteNoisePicardMap D hsigma T U := by
  have hpath := strongSolution_eq_version hXeq D hb hsigma Z0 hZ0 hmem hX
  have hprod := (Measure.quasiMeasurePreserving_snd
    (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hpath
  have hcut : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun p => X p.1 p.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
      ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun p => version D hb hsigma Z0 T U p.1 p.2)) := by
    filter_upwards [hprod] with p hp
    by_cases ht : p.1 ∈ Ioc 0 T
    · simp only [show p ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨ht, mem_univ _⟩, indicator_of_mem]
      exact hp p.1 ht.2
    · simp [ht]
  apply Subtype.ext
  apply Lp.ext
  exact hXeq.symm.trans (hcut.trans (version_timeCut_eq_picard D hb hsigma Z0 hZ0 hmem T U))
end ActualSolution

theorem strongSolution_on_smaller (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) {S T : ℝ≥0} (hST : S ≤ T)
    {X : ℝ≥0 → Ω → State N} {U : PredictableStateL2 N F P}
    (hXeq : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun p => X p.1 p.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
    (hX : IsStrongSolutionOn b sigma (fun i j => (hsigma i j).continuous) D Z0 X T) :
    IsStrongSolutionOn b sigma (fun i j => (hsigma i j).continuous) D Z0 X S := by
  rcases hX with ⟨hXa,hXc,hbmem,hsigmamem,hactual⟩
  refine ⟨hXa,hXc,(fun i => coefficient_timeCut_memLp hXeq (hb i) S hST),
    (fun i j t ht => hsigmamem i j t (ht.trans hST)), ?_⟩
  intro t ht i
  exact hactual t (ht.trans hST) i


@[expose] def horizonClass (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) (T : ℝ≥0) : PredictableStateL2 N F P :=
  (GlobalSDE.exists_unique_picard_fixedPoint D hb hsigma T (initialClass Z0 hZ0 hmem T)).choose

theorem horizonClass_fixedPoint (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) (T : ℝ≥0) : horizonClass D hb hsigma Z0 hZ0 hmem T = initialClass Z0 hZ0 hmem T +
      finiteDriftPicardMap hb T (horizonClass D hb hsigma Z0 hZ0 hmem T) +
      finiteNoisePicardMap D hsigma T (horizonClass D hb hsigma Z0 hZ0 hmem T) :=
  (GlobalSDE.exists_unique_picard_fixedPoint D hb hsigma T (initialClass Z0 hZ0 hmem T)).choose_spec.1

theorem horizonClass_unique (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) (T : ℝ≥0) (V : PredictableStateL2 N F P)
    (hV : V = initialClass Z0 hZ0 hmem T + finiteDriftPicardMap hb T V + finiteNoisePicardMap D hsigma T V) :
    V = horizonClass D hb hsigma Z0 hZ0 hmem T :=
  (GlobalSDE.exists_unique_picard_fixedPoint D hb hsigma T (initialClass Z0 hZ0 hmem T)).choose_spec.2 V hV

@[expose] def horizonProcess (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) (T : ℝ≥0) : ℝ≥0 → Ω → State N :=
  version D hb hsigma Z0 T (horizonClass D hb hsigma Z0 hZ0 hmem T)

theorem horizonProcess_stronglyAdapted (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) (T : ℝ≥0) : StronglyAdapted F (horizonProcess D hb hsigma Z0 hZ0 hmem T) :=
  version_stronglyAdapted D hb hsigma Z0 hZ0 T _

theorem horizonProcess_continuous (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) (T : ℝ≥0) : ∀ᵐ omega ∂P, Continuous (fun t => horizonProcess D hb hsigma Z0 hZ0 hmem T t omega) :=
  version_continuous D hb hsigma Z0 T _

theorem horizonProcess_strongSolution (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) (T : ℝ≥0) : IsStrongSolutionOn b sigma (fun i j => (hsigma i j).continuous) D Z0
      (horizonProcess D hb hsigma Z0 hZ0 hmem T) T :=
  strongSolution_of_picard_fixedPoint D hb hsigma Z0 hZ0 hmem T _ (horizonClass_fixedPoint D hb hsigma Z0 hZ0 hmem T)

theorem horizonProcess_timeCut (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) (T : ℝ≥0) :
    ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun p => horizonProcess D hb hsigma Z0 hZ0 hmem T p.1 p.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
      (horizonClass D hb hsigma Z0 hZ0 hmem T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) :=
  version_timeCut_eq_fixedPoint D hb hsigma Z0 hZ0 hmem T _ (horizonClass_fixedPoint D hb hsigma Z0 hZ0 hmem T)

theorem horizonProcess_compatible (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) {S T : ℝ≥0} (hST : S ≤ T) :
    ∀ᵐ omega ∂P, ∀ t, t ≤ S → horizonProcess D hb hsigma Z0 hZ0 hmem T t omega = horizonProcess D hb hsigma Z0 hZ0 hmem S t omega :=
by
  have hVeq := horizonProcess_timeCut D hb hsigma Z0 hZ0 hmem T
  have hXsol := horizonProcess_strongSolution D hb hsigma Z0 hZ0 hmem T
  have hXsmall := strongSolution_on_smaller D hb hsigma Z0 hST hVeq hXsol
  have hXeq := StrongUniqueness.stateTimeRestrict_of_process hST hVeq
  have hWfix := strongSolution_fixedPoint hXeq D hb hsigma Z0 hZ0 hmem hXsmall
  have hWU := horizonClass_unique D hb hsigma Z0 hZ0 hmem S _ hWfix
  have hpath := strongSolution_eq_version hXeq D hb hsigma Z0 hZ0 hmem hXsmall
  rw [hWU] at hpath
  exact hpath

theorem horizonProcess_compatible_pair (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) (S T : ℝ≥0) :
    ∀ᵐ omega ∂P, ∀ t, t ≤ S → t ≤ T →
      horizonProcess D hb hsigma Z0 hZ0 hmem S t omega = horizonProcess D hb hsigma Z0 hZ0 hmem T t omega := by
  rcases le_total S T with hST | hTS
  · exact (horizonProcess_compatible D hb hsigma Z0 hZ0 hmem hST).mono (fun _ h t ht _ => (h t ht).symm)
  · exact (horizonProcess_compatible D hb hsigma Z0 hZ0 hmem hTS).mono (fun _ h t _ ht => h t ht)

@[expose] def integerHorizon (n : ℕ) : ℝ≥0 := n+1

@[expose] def process (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) (t : ℝ≥0) (omega : Ω) : State N :=
  horizonProcess D hb hsigma Z0 hZ0 hmem (integerHorizon (Nat.ceil t)) t omega

theorem le_integerHorizon_ceil (t : ℝ≥0) : t ≤ integerHorizon (Nat.ceil t) :=
  (Nat.le_ceil t).trans (by simp [integerHorizon])

theorem process_stronglyAdapted (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) : StronglyAdapted F (process D hb hsigma Z0 hZ0 hmem) := fun t =>
  horizonProcess_stronglyAdapted D hb hsigma Z0 hZ0 hmem _ t

/-- The all-time process agrees on a common path event with each of its
finite-horizon solutions throughout that horizon. -/
theorem process_eq_horizon (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) (T : ℝ≥0) : ∀ᵐ omega ∂P, ∀ t, t ≤ T →
      process D hb hsigma Z0 hZ0 hmem t omega = horizonProcess D hb hsigma Z0 hZ0 hmem T t omega := by
  have hall := ae_all_iff.mpr (fun n : ℕ => horizonProcess_compatible_pair D hb hsigma Z0 hZ0 hmem (integerHorizon n) T)
  filter_upwards [hall] with omega homega
  intro t ht
  exact homega (Nat.ceil t) t (le_integerHorizon_ceil t) ht

theorem process_continuous (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) : ∀ᵐ omega ∂P, Continuous (fun t => process D hb hsigma Z0 hZ0 hmem t omega) := by
  have heq := ae_all_iff.mpr (fun n : ℕ => process_eq_horizon D hb hsigma Z0 hZ0 hmem (integerHorizon n))
  have hcts := ae_all_iff.mpr (fun n : ℕ => horizonProcess_continuous D hb hsigma Z0 hZ0 hmem (integerHorizon n))
  filter_upwards [heq,hcts] with omega homega hcont
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨n,hn⟩ := exists_nat_gt t
  have htn : t < integerHorizon n := hn.trans_le (by simp [integerHorizon])
  have hlocal : (fun s => process D hb hsigma Z0 hZ0 hmem s omega) =ᶠ[𝓝 t]
      (fun s => horizonProcess D hb hsigma Z0 hZ0 hmem (integerHorizon n) s omega) := by
    filter_upwards [eventually_lt_nhds htn] with s hs
    exact homega n s hs.le
  exact (continuousAt_congr hlocal).mpr (hcont n).continuousAt

/-- Actual predictable state class of the all-time process on every finite
horizon. It is identified with the constructed Picard fixed point. -/
theorem process_timeCut (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) (T : ℝ≥0) :
    ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun p => process D hb hsigma Z0 hZ0 hmem p.1 p.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
      (horizonClass D hb hsigma Z0 hZ0 hmem T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) := by
  have hprod := (Measure.quasiMeasurePreserving_snd
    (μ := nonnegativeLebesgueMeasure) (ν := P)).ae (process_eq_horizon D hb hsigma Z0 hZ0 hmem T)
  apply EventuallyEq.trans _ (horizonProcess_timeCut D hb hsigma Z0 hZ0 hmem T)
  filter_upwards [hprod] with p hp
  by_cases hpt : p.1 ∈ Ioc 0 T
  · simp only [show p ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨hpt,mem_univ _⟩,indicator_of_mem]
    exact hp p.1 hpt.2
  · simp [hpt]

/-- The all-time process satisfies the real dt and actual full-filtration
matrix Itô equation on every finite horizon. -/
theorem process_strongSolution (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) (T : ℝ≥0) : IsStrongSolutionOn b sigma (fun i j => (hsigma i j).continuous) D Z0
      (process D hb hsigma Z0 hZ0 hmem) T := by
  have hXa := process_stronglyAdapted D hb hsigma Z0 hZ0 hmem
  have hXc := process_continuous D hb hsigma Z0 hZ0 hmem
  have hXeq := process_timeCut D hb hsigma Z0 hZ0 hmem T
  refine ⟨hXa,hXc,(fun i => coefficient_timeCut_memLp hXeq (hb i) T le_rfl),
    (fun i j t ht => coefficient_timeCut_memLp hXeq (hsigma i j) t ht), ?_⟩
  intro t ht i
  filter_upwards [process_eq_horizon D hb hsigma Z0 hZ0 hmem T, driftVersion_eq_actual_drift_ae hXeq (hb i),
    actual_driverIto_ae_eq hXeq hXa hXc D (hsigma i) t ht] with omega hprefix hdrift hnoise
  rw [hprefix t ht]
  change (version D hb hsigma Z0 T (horizonClass D hb hsigma Z0 hZ0 hmem T) t omega) i = _
  rw [version_apply,hnoise]
  simp only [hdrift t ht]

theorem exists_global_strongSolution (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) : ∃ X : ℝ≥0 → Ω → State N, StronglyAdapted F X ∧
      (∀ᵐ omega ∂P, Continuous (fun t => X t omega)) ∧
      ∀ T : ℝ≥0, IsStrongSolutionOn b sigma (fun i j => (hsigma i j).continuous) D Z0 X T :=
  ⟨process D hb hsigma Z0 hZ0 hmem,process_stronglyAdapted D hb hsigma Z0 hZ0 hmem,process_continuous D hb hsigma Z0 hZ0 hmem,
    process_strongSolution D hb hsigma Z0 hZ0 hmem⟩


end SphericalAging.RandomInitialSDE
