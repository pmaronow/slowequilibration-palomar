module

public import SphericalAging.CutoffSDE
public import SphericalAging.NullAugmentation

public section

/-! Actual all-path continuous adapted local SDE solutions on the proved
null augmentation, preserving their genuine matrix Itô integral equation. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.AllPathSDE
open HardSphereDynamics LocalSDE
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem timeCut_path_congr {X Y : ℝ≥0 → Ω → State N}
    (hYX : ∀ᵐ omega ∂P, ∀ t, Y t omega = X t omega) (g : State N → ℝ) (t : ℝ≥0) :
    FourPapersCommon.continuousAdaptedTimeCut (fun s omega => g (Y s omega)) t
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        FourPapersCommon.continuousAdaptedTimeCut (fun s omega => g (X s omega)) t := by
  have hae := (Measure.quasiMeasurePreserving_snd
    (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hYX
  filter_upwards [hae] with q hq
  simp only [FourPapersCommon.continuousAdaptedTimeCut, hq q.1]

theorem coefficientPredictableActual_congr {X Y : ℝ≥0 → Ω → State N}
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ omega ∂P, Continuous (fun s => X s omega))
    (hYa : StronglyAdapted F Y) (hYc : ∀ᵐ omega ∂P, Continuous (fun s => Y s omega))
    (hYX : ∀ᵐ omega ∂P, ∀ t, Y t omega = X t omega)
    {g : State N → ℝ} (hg : Continuous g) (t : ℝ≥0)
    (hmemX : MemLp (FourPapersCommon.continuousAdaptedTimeCut (fun s omega => g (X s omega)) t)
      2 (nonnegativeLebesgueMeasure.prod P))
    (hmemY : MemLp (FourPapersCommon.continuousAdaptedTimeCut (fun s omega => g (Y s omega)) t)
      2 (nonnegativeLebesgueMeasure.prod P)) :
    coefficientPredictableActual hYa hYc hg t hmemY =
      coefficientPredictableActual hXa hXc hg t hmemX := by
  apply Subtype.ext
  apply Lp.ext
  exact hmemY.coeFn_toLp.trans ((timeCut_path_congr hYX g t).trans hmemX.coeFn_toLp.symm)

/-- Null path changes preserve the actual strong SDE equation in the same
filtration; the stochastic integrals are identified in their actual L²
classes, not assumed equal as versions. -/
theorem IsLocalStrongSolutionOn.path_congr {b : Fin N → State N → ℝ}
    {sigma : Fin N → Fin N → State N → ℝ} {hsigma : ∀ i j, Continuous (sigma i j)}
    {D : BrownianDriver N P F} {x0 : State N} {X Y : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (hX : IsLocalStrongSolutionOn b sigma hsigma D x0 X T)
    (hYa : StronglyAdapted F Y) (hYc : ∀ᵐ omega ∂P, Continuous (fun s => Y s omega))
    (hYX : ∀ᵐ omega ∂P, ∀ t, Y t omega = X t omega) :
    IsLocalStrongSolutionOn b sigma hsigma D x0 Y T := by
  rcases hX with ⟨hXa, hXc, hbX, hsigmaX, hXeq⟩
  have hbY : ∀ i, MemLp (FourPapersCommon.continuousAdaptedTimeCut
      (fun s omega => b i (Y s omega)) T) 2 (nonnegativeLebesgueMeasure.prod P) :=
    fun i => (hbX i).ae_eq (timeCut_path_congr hYX (b i) T).symm
  have hsigmaY : ∀ i j (t : ℝ≥0), t ≤ T → MemLp
      (FourPapersCommon.continuousAdaptedTimeCut (fun s omega => sigma i j (Y s omega)) t)
      2 (nonnegativeLebesgueMeasure.prod P) :=
    fun i j t ht => (hsigmaX i j t ht).ae_eq (timeCut_path_congr hYX (sigma i j) t).symm
  refine ⟨hYa, hYc, hbY, hsigmaY, ?_⟩
  intro t ht i
  have hnoise : driverItoMap D (fun j => coefficientPredictableActual hYa hYc (hsigma i j) t
      (hsigmaY i j t ht)) = driverItoMap D (fun j => coefficientPredictableActual hXa hXc (hsigma i j) t
        (hsigmaX i j t ht)) := by
    congr 1
    funext j
    exact coefficientPredictableActual_congr hXa hXc hYa hYc hYX (hsigma i j) t _ _
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

/-- The concrete manuscript cutoff SDE has a local strongly adapted solution
whose every path is continuous, on a constructively augmented genuine
Brownian filtration. -/
theorem exists_allPath_cutoff_hamiltonian_strongSolution
    (D : BrownianDriver N P F) (β : ℝ) (J : FiniteModel.Disorder N p)
    (R : ℝ) (hR : 0 < R) (x0 : State N) :
    ∃ T : ℝ≥0, 0 < T ∧ ∃ X : ℝ≥0 → Ω → State N,
      (∀ omega, Continuous (fun t => X t omega)) ∧
      ∃ hsigma : ∀ i j, Continuous (CutoffSDE.cutoffNoise N R hR i j),
        IsLocalStrongSolutionOn (CutoffSDE.cutoffDrift β J R hR) (CutoffSDE.cutoffNoise N R hR)
          hsigma (NullAugmentation.driver D) x0 X T := by
  obtain ⟨T, hT, X, hsigma, hX⟩ := CutoffSDE.exists_cutoff_hamiltonian_strongSolution
    (NullAugmentation.driver D) β J R hR x0
  obtain ⟨hXa, hXc, hbmem, hsigmamem, heq⟩ := hX
  have hXsol : IsLocalStrongSolutionOn (CutoffSDE.cutoffDrift β J R hR) (CutoffSDE.cutoffNoise N R hR)
      hsigma (NullAugmentation.driver D) x0 X T := ⟨hXa, hXc, hbmem, hsigmamem, heq⟩
  obtain ⟨Y, hYa, hYc, hYX⟩ := NullAugmentation.exists_allPath_continuous_modification_augmented
    F X hXa hXc
  exact ⟨T, hT, Y, hYc, hsigma, IsLocalStrongSolutionOn.path_congr hXsol hYa (.of_forall hYc) hYX⟩

end SphericalAging.AllPathSDE
