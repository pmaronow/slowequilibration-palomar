module

public import SphericalAging.StrongUniqueness
public import SphericalAging.WeightedItoNorm
public import SphericalAging.WeightedDriftNorm

public section

/-! Actual global-in-time strong solutions for finite-dimensional globally
Lipschitz matrix-driven SDEs. Exponential weighting constructs a unique
predictable fixed point on every finite horizon. Actual integral uniqueness
then proves consistency of the horizon solutions and their all-time limit. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.GlobalSDE
open HardSphereDynamics PredictableItoTime PredictableDriftTime LocalSDE WeightedPredictable
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem exists_unique_picard_fixedPoint (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (T : ℝ≥0) (A : PredictableStateL2 N F P) :
    ∃ U : PredictableStateL2 N F P, U = A + finiteDriftPicardMap hb T U + finiteNoisePicardMap D hsigma T U ∧
      ∀ V, V = A + finiteDriftPicardMap hb T V + finiteNoisePicardMap D hsigma T V → V = U := by
  obtain ⟨α,hα,Cd,Ci,hCd,hCi,hsmall⟩ := WeightedPicard.exists_contraction_parameters N Kb Ks T
  apply WeightedPicard.exists_unique_picard_fixedPoint_of_operator_bounds D hb hsigma α T Cd Ci A
  · intro V
    rw [hCd]
    exact WeightedDriftNorm.norm_weighted_driftVolterra_le hα T V
  · intro j V
    rw [hCi, one_div]
    exact WeightedItoNorm.norm_weighted_itoVolterra_le (D.brownian j)
      (D.coordinateStronglyMeasurable j) (D.filtered j) hα T V
  · exact hsmall

@[expose] def horizonClass (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) (T : ℝ≥0) : PredictableStateL2 N F P :=
  (exists_unique_picard_fixedPoint D hb hsigma T (initialClass (F := F) (P := P) x0 T)).choose

theorem horizonClass_fixedPoint (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) (T : ℝ≥0) : horizonClass D hb hsigma x0 T = initialClass (F := F) (P := P) x0 T +
      finiteDriftPicardMap hb T (horizonClass D hb hsigma x0 T) +
      finiteNoisePicardMap D hsigma T (horizonClass D hb hsigma x0 T) :=
  (exists_unique_picard_fixedPoint D hb hsigma T (initialClass (F := F) (P := P) x0 T)).choose_spec.1

theorem horizonClass_unique (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) (T : ℝ≥0) (V : PredictableStateL2 N F P)
    (hV : V = initialClass (F := F) (P := P) x0 T + finiteDriftPicardMap hb T V + finiteNoisePicardMap D hsigma T V) :
    V = horizonClass D hb hsigma x0 T :=
  (exists_unique_picard_fixedPoint D hb hsigma T (initialClass (F := F) (P := P) x0 T)).choose_spec.2 V hV

@[expose] def horizonProcess (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) (T : ℝ≥0) : ℝ≥0 → Ω → State N :=
  version D hb hsigma x0 T (horizonClass D hb hsigma x0 T)

theorem horizonProcess_stronglyAdapted (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) (T : ℝ≥0) : StronglyAdapted F (horizonProcess D hb hsigma x0 T) :=
  version_stronglyAdapted D hb hsigma x0 T _

theorem horizonProcess_continuous (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) (T : ℝ≥0) : ∀ᵐ omega ∂P, Continuous (fun t => horizonProcess D hb hsigma x0 T t omega) :=
  version_ae_continuous D hb hsigma x0 T _

theorem horizonProcess_strongSolution (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) (T : ℝ≥0) : IsLocalStrongSolutionOn b sigma (fun i j => (hsigma i j).continuous) D x0
      (horizonProcess D hb hsigma x0 T) T :=
  WeightedPicard.strongSolution_of_picard_fixedPoint D hb hsigma x0 T _ (horizonClass_fixedPoint D hb hsigma x0 T)

theorem horizonProcess_timeCut (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) (T : ℝ≥0) :
    ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun p => horizonProcess D hb hsigma x0 T p.1 p.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
      (horizonClass D hb hsigma x0 T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) :=
  version_timeCut_eq_fixedPoint_ae D hb hsigma x0 T _ (horizonClass_fixedPoint D hb hsigma x0 T)

theorem horizonProcess_compatible (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) {S T : ℝ≥0} (hST : S ≤ T) :
    ∀ᵐ omega ∂P, ∀ t, t ≤ S → horizonProcess D hb hsigma x0 T t omega = horizonProcess D hb hsigma x0 S t omega :=
  StrongUniqueness.picard_versions_compatible D hb hsigma x0 hST _ _
    (horizonClass_fixedPoint D hb hsigma x0 S) (horizonClass_fixedPoint D hb hsigma x0 T)
    (horizonClass_unique D hb hsigma x0 S)

theorem horizonProcess_compatible_pair (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) (S T : ℝ≥0) :
    ∀ᵐ omega ∂P, ∀ t, t ≤ S → t ≤ T →
      horizonProcess D hb hsigma x0 S t omega = horizonProcess D hb hsigma x0 T t omega := by
  rcases le_total S T with hST | hTS
  · exact (horizonProcess_compatible D hb hsigma x0 hST).mono (fun _ h t ht _ => (h t ht).symm)
  · exact (horizonProcess_compatible D hb hsigma x0 hTS).mono (fun _ h t _ ht => h t ht)

@[expose] def integerHorizon (n : ℕ) : ℝ≥0 := n+1

@[expose] def process (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) (t : ℝ≥0) (omega : Ω) : State N :=
  horizonProcess D hb hsigma x0 (integerHorizon (Nat.ceil t)) t omega

theorem le_integerHorizon_ceil (t : ℝ≥0) : t ≤ integerHorizon (Nat.ceil t) :=
  (Nat.le_ceil t).trans (by simp [integerHorizon])

theorem process_stronglyAdapted (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) : StronglyAdapted F (process D hb hsigma x0) := fun t =>
  horizonProcess_stronglyAdapted D hb hsigma x0 _ t

/-- The all-time process agrees on a common path event with each of its
finite-horizon solutions throughout that horizon. -/
theorem process_eq_horizon (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) (T : ℝ≥0) : ∀ᵐ omega ∂P, ∀ t, t ≤ T →
      process D hb hsigma x0 t omega = horizonProcess D hb hsigma x0 T t omega := by
  have hall := ae_all_iff.mpr (fun n : ℕ => horizonProcess_compatible_pair D hb hsigma x0 (integerHorizon n) T)
  filter_upwards [hall] with omega homega
  intro t ht
  exact homega (Nat.ceil t) t (le_integerHorizon_ceil t) ht

theorem process_continuous (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) : ∀ᵐ omega ∂P, Continuous (fun t => process D hb hsigma x0 t omega) := by
  have heq := ae_all_iff.mpr (fun n : ℕ => process_eq_horizon D hb hsigma x0 (integerHorizon n))
  have hcts := ae_all_iff.mpr (fun n : ℕ => horizonProcess_continuous D hb hsigma x0 (integerHorizon n))
  filter_upwards [heq,hcts] with omega homega hcont
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨n,hn⟩ := exists_nat_gt t
  have htn : t < integerHorizon n := hn.trans_le (by simp [integerHorizon])
  have hlocal : (fun s => process D hb hsigma x0 s omega) =ᶠ[𝓝 t]
      (fun s => horizonProcess D hb hsigma x0 (integerHorizon n) s omega) := by
    filter_upwards [eventually_lt_nhds htn] with s hs
    exact homega n s hs.le
  exact (continuousAt_congr hlocal).mpr (hcont n).continuousAt

/-- Actual predictable state class of the all-time process on every finite
horizon. It is identified with the constructed Picard fixed point. -/
theorem process_timeCut (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) (T : ℝ≥0) :
    ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun p => process D hb hsigma x0 p.1 p.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
      (horizonClass D hb hsigma x0 T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) := by
  have hprod := (Measure.quasiMeasurePreserving_snd
    (μ := nonnegativeLebesgueMeasure) (ν := P)).ae (process_eq_horizon D hb hsigma x0 T)
  apply EventuallyEq.trans _ (horizonProcess_timeCut D hb hsigma x0 T)
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
    (x0 : State N) (T : ℝ≥0) : IsLocalStrongSolutionOn b sigma (fun i j => (hsigma i j).continuous) D x0
      (process D hb hsigma x0) T := by
  have hXa := process_stronglyAdapted D hb hsigma x0
  have hXc := process_continuous D hb hsigma x0
  have hXeq := process_timeCut D hb hsigma x0 T
  refine ⟨hXa,hXc,(fun i => coefficient_timeCut_memLp hXeq (hb i) T le_rfl),
    (fun i j t ht => coefficient_timeCut_memLp hXeq (hsigma i j) t ht), ?_⟩
  intro t ht i
  filter_upwards [process_eq_horizon D hb hsigma x0 T, driftVersion_eq_actual_drift_ae hXeq (hb i),
    actual_driverIto_ae_eq hXeq hXa hXc D (hsigma i) t ht] with omega hprefix hdrift hnoise
  rw [hprefix t ht]
  change (version D hb hsigma x0 T (horizonClass D hb hsigma x0 T) t omega) i = _
  rw [version_apply,hnoise]
  simp only [coordinateVersion,hdrift t ht]

theorem exists_global_strongSolution (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) : ∃ X : ℝ≥0 → Ω → State N, StronglyAdapted F X ∧
      (∀ᵐ omega ∂P, Continuous (fun t => X t omega)) ∧
      ∀ T : ℝ≥0, IsLocalStrongSolutionOn b sigma (fun i j => (hsigma i j).continuous) D x0 X T :=
  ⟨process D hb hsigma x0,process_stronglyAdapted D hb hsigma x0,process_continuous D hb hsigma x0,
    process_strongSolution D hb hsigma x0⟩

/-- Genuine arbitrary-horizon strong-solution uniqueness. The state-class
premises assert only the actual predictable L² regularity, which bounded
sphere paths supply; no uniqueness or fixed-point premise remains. -/
theorem strongSolution_unique_of_stateClasses (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) (T : ℝ≥0)
    {X Y : ℝ≥0 → Ω → State N} {U V : PredictableStateL2 N F P}
    (hXeq : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun p => X p.1 p.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
    (hYeq : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun p => Y p.1 p.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (V : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
    (hX : IsLocalStrongSolutionOn b sigma (fun i j => (hsigma i j).continuous) D x0 X T)
    (hY : IsLocalStrongSolutionOn b sigma (fun i j => (hsigma i j).continuous) D x0 Y T) :
    ∀ᵐ omega ∂P, ∀ t, t ≤ T → X t omega = Y t omega := by
  apply StrongUniqueness.strongSolutions_eq_of_picard_unique D hb hsigma x0 T _ hXeq hYeq hX hY
  intro U V hU hV
  exact (horizonClass_unique D hb hsigma x0 T U hU).trans (horizonClass_unique D hb hsigma x0 T V hV).symm

end SphericalAging.GlobalSDE
